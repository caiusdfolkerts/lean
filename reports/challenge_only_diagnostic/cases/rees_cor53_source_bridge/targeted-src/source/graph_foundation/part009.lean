module
public import graph_foundation.part008

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Symmetric.Vendor.RingTheory.MvPolynomial.Groebner.NormalForm -/
section

section
noncomputable section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Standard monomials and normal forms

Let `m` be a monomial order on `σ →₀ ℕ` and `I` an ideal of `MvPolynomial σ R`. The *standard
monomials* of `I` are the exponents that are not divisible by the leading monomial of any nonzero
element of `I`. This file proves that the standard monomials give an `R`-basis of the quotient
`MvPolynomial σ R ⧸ I` as soon as `I` has a Gröbner basis whose nonzero members have unit leading
coefficients, and constructs the corresponding linear normal-form map.

* `MonomialOrder.standardMonomials m I`: the standard monomials of `I`.
* `MonomialOrder.IsGroebnerBasis.restrictSupportEquivQuotient`: the polynomials supported on the
  standard monomials of `I` are linearly isomorphic to `MvPolynomial σ R ⧸ I` through the quotient
  map.
* `MonomialOrder.IsGroebnerBasis.basisQuotient`: the images of the standard monomials form a basis
  of `MvPolynomial σ R ⧸ I`.
* `MonomialOrder.IsGroebnerBasis.normalForm`: the `R`-linear map sending `f` to the unique
  polynomial supported on the standard monomials that is congruent to `f` modulo `I`.

## Main results

* `MonomialOrder.disjoint_restrictSupport_standardMonomials`: no nonzero polynomial supported on
  the standard monomials of `I` lies in `I`. This holds for every ideal, with no Gröbner basis.
* `MonomialOrder.standardMonomials_span_leadingTerm`: `I` and its ideal of leading terms have the
  same standard monomials.
* `MonomialOrder.IsGroebnerBasis.normalForm_eq_iff`: `normalForm f` is characterized as the
  polynomial supported on the standard monomials that is congruent to `f` modulo `I`.
* `MonomialOrder.IsGroebnerBasis.isRemainder_iff_eq_normalForm`: the remainders of `f` on division
  by the Gröbner basis are exactly its normal form.
* `MonomialOrder.IsGroebnerBasis.ker_normalForm`, `MonomialOrder.IsGroebnerBasis.range_normalForm`,
  `MonomialOrder.IsGroebnerBasis.normalForm_normalForm` and
  `MonomialOrder.IsGroebnerBasis.normalForm_normalForm_mul`: the normal form is an idempotent
  linear map with kernel `I`, image the polynomials supported on the standard monomials, and
  compatible with multiplication in the quotient.

Over a field every ideal `I` is a Gröbner basis of itself (`MonomialOrder.isGroebnerBasis_self`)
and every nonzero polynomial has a unit leading coefficient (`MonomialOrder.isUnit_leadingCoeff`),
so the results above apply to every ideal.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 2, §6, Proposition 1,
  and Chapter 5, §3, Proposition 1.
-/


namespace MonomialOrder

open MvPolynomial

variable {σ R : Type*} (m : MonomialOrder σ)

section CommSemiring

variable [CommSemiring R]

/-- The standard monomials of the ideal `I` for the monomial order `m`: the exponents that are not
divisible by the leading monomial of any nonzero element of `I`. -/
def standardMonomials (I : Ideal (MvPolynomial σ R)) : Set (σ →₀ ℕ) :=
  {c | ∀ p ∈ I, p ≠ 0 → ¬ m.degree p ≤ c}

variable {m} {I : Ideal (MvPolynomial σ R)} {G : Set (MvPolynomial σ R)} {c : σ →₀ ℕ}
  {f r : MvPolynomial σ R}

/-- An exponent is a standard monomial of `I` when it is not divisible by the leading monomial of
any nonzero element of `I`. -/
@[simp]
theorem mem_standardMonomials_iff :
    c ∈ m.standardMonomials I ↔ ∀ p ∈ I, p ≠ 0 → ¬ m.degree p ≤ c :=
  Iff.rfl

variable (m I) in
/-- An ideal and its ideal of leading terms have the same standard monomials. -/
@[simp]
theorem standardMonomials_span_leadingTerm :
    m.standardMonomials (Ideal.span (m.leadingTerm '' (I : Set (MvPolynomial σ R)))) =
      m.standardMonomials I := by
  ext c
  simp only [mem_standardMonomials_iff]
  refine ⟨fun hc p hp hp0 hpc ↦ ?_, fun hc q hq hq0 hqc ↦ ?_⟩
  · exact hc _ (Ideal.subset_span ⟨p, hp, rfl⟩) ((m.leadingTerm_eq_zero_iff p).not.2 hp0)
      ((m.degree_leadingTerm p).symm ▸ hpc)
  · obtain ⟨p, hp, hp0, hpq⟩ := exists_degree_le_of_mem_span_leadingTerm hq
      (m.degree_mem_support hq0)
    exact hc p hp hp0 (hpq.trans hqc)

/-- The standard monomials of `I` are the exponents not divisible by the leading monomial of a
nonzero element of a Gröbner basis of `I`. -/
theorem IsGroebnerBasis.mem_standardMonomials_iff (h : m.IsGroebnerBasis G I) :
    c ∈ m.standardMonomials I ↔ ∀ g ∈ G, g ≠ 0 → ¬ m.degree g ≤ c := by
  rw [MonomialOrder.mem_standardMonomials_iff]
  refine ⟨fun hc g hg ↦ hc g (h.subset hg), fun hc p hp hp0 hpc ↦ ?_⟩
  obtain ⟨g, hgG, hg0, hgp⟩ := h.exists_degree_le_degree hp hp0
  exact hc g hgG hg0 (hgp.trans hpc)

/-- A polynomial is its own remainder on division by a Gröbner basis of `I` exactly when it is
supported on the standard monomials of `I`. -/
theorem IsGroebnerBasis.isRemainder_self_iff (h : m.IsGroebnerBasis G I) :
    m.IsRemainder r G r ↔ r ∈ restrictSupport R (m.standardMonomials I) := by
  simp_rw [MonomialOrder.isRemainder_self_iff, mem_restrictSupport_iff, Set.subset_def,
    Finset.mem_coe, h.mem_standardMonomials_iff]

/-- Every remainder on division by a Gröbner basis of `I` is supported on the standard monomials
of `I`. -/
theorem IsGroebnerBasis.mem_restrictSupport_of_isRemainder (h : m.IsGroebnerBasis G I)
    (hr : m.IsRemainder f G r) : r ∈ restrictSupport R (m.standardMonomials I) :=
  h.isRemainder_self_iff.1 <| MonomialOrder.isRemainder_self_iff.2 fun _ hc _ hb hb0 ↦
    hr.not_degree_le hc hb hb0

variable (m I) in
/-- No nonzero polynomial supported on the standard monomials of `I` lies in `I`. -/
theorem disjoint_restrictSupport_standardMonomials :
    Disjoint (restrictSupport R (m.standardMonomials I)) (I.restrictScalars R) := by
  refine Submodule.disjoint_def.2 fun p hp hpI ↦ by_contra fun hp0 ↦ ?_
  exact mem_standardMonomials_iff.1 ((mem_restrictSupport_iff R).1 hp (m.degree_mem_support hp0))
    p ((Submodule.restrictScalars_mem _ _ _).1 hpI) hp0 le_rfl

end CommSemiring

section CommRing

variable [CommRing R] {m} {I : Ideal (MvPolynomial σ R)} {G : Set (MvPolynomial σ R)}
  {f g r r₁ r₂ : MvPolynomial σ R}

/-- Two polynomials supported on the standard monomials of `I` that are congruent modulo `I` are
equal. -/
theorem eq_of_sub_mem_of_mem_restrictSupport
    (hr₁ : r₁ ∈ restrictSupport R (m.standardMonomials I))
    (hr₂ : r₂ ∈ restrictSupport R (m.standardMonomials I)) (hr : r₁ - r₂ ∈ I) : r₁ = r₂ :=
  sub_eq_zero.1 <| Submodule.disjoint_def.1 (disjoint_restrictSupport_standardMonomials m I) _
    (Submodule.sub_mem _ hr₁ hr₂) hr

/-- Given a Gröbner basis of `I` whose nonzero members have unit leading coefficients, every
polynomial is congruent modulo `I` to a polynomial supported on the standard monomials of `I`. -/
theorem IsGroebnerBasis.exists_mem_restrictSupport_sub_mem (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) (f : MvPolynomial σ R) :
    ∃ r ∈ restrictSupport R (m.standardMonomials I), f - r ∈ I := by
  obtain ⟨r, hr⟩ := exists_isRemainder hG f
  exact ⟨r, h.mem_restrictSupport_of_isRemainder hr, Ideal.span_le.2 h.subset hr.sub_mem_span⟩

/-- Given a Gröbner basis of `I` whose nonzero members have unit leading coefficients, the
quotient map restricts to a linear isomorphism from the polynomials supported on the standard
monomials of `I` onto `MvPolynomial σ R ⧸ I`. -/
noncomputable def IsGroebnerBasis.restrictSupportEquivQuotient (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    restrictSupport R (m.standardMonomials I) ≃ₗ[R] MvPolynomial σ R ⧸ I :=
  LinearEquiv.ofBijective
    ((Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ (restrictSupport R (m.standardMonomials I)).subtype)
    ⟨fun r₁ r₂ hr ↦ Subtype.ext <| eq_of_sub_mem_of_mem_restrictSupport r₁.2 r₂.2 <|
        Ideal.Quotient.eq.1 hr,
      fun x ↦ by
        obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
        obtain ⟨r, hr, hfr⟩ := h.exists_mem_restrictSupport_sub_mem hG f
        exact ⟨⟨r, hr⟩, (Ideal.Quotient.eq.2 hfr).symm⟩⟩

/-- `MonomialOrder.IsGroebnerBasis.restrictSupportEquivQuotient` is the quotient map. -/
@[simp]
theorem IsGroebnerBasis.restrictSupportEquivQuotient_apply (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (r : restrictSupport R (m.standardMonomials I)) :
    h.restrictSupportEquivQuotient hG r = Ideal.Quotient.mk I (r : MvPolynomial σ R) :=
  (rfl)

/-- **The standard monomial basis.** Given a Gröbner basis of `I` whose nonzero members have unit
leading coefficients, the images of the standard monomials of `I` form an `R`-basis of
`MvPolynomial σ R ⧸ I`. -/
noncomputable def IsGroebnerBasis.basisQuotient (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    Module.Basis (m.standardMonomials I) R (MvPolynomial σ R ⧸ I) :=
  (basisRestrictSupport R _).map (h.restrictSupportEquivQuotient hG)

@[simp]
theorem IsGroebnerBasis.basisQuotient_apply (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) (c : m.standardMonomials I) :
    h.basisQuotient hG c = Ideal.Quotient.mk I (monomial (c : σ →₀ ℕ) 1) := by
  simp [basisQuotient]

/-- **The normal form** modulo an ideal `I` with a Gröbner basis whose nonzero members have unit
leading coefficients: the `R`-linear map sending `f` to the unique polynomial supported on the
standard monomials of `I` that is congruent to `f` modulo `I`
(`MonomialOrder.IsGroebnerBasis.normalForm_eq_iff`). -/
noncomputable def IsGroebnerBasis.normalForm (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (restrictSupport R (m.standardMonomials I)).subtype ∘ₗ
    (h.restrictSupportEquivQuotient hG).symm.toLinearMap ∘ₗ (Ideal.Quotient.mkₐ R I).toLinearMap

/-- The inverse of `MonomialOrder.IsGroebnerBasis.restrictSupportEquivQuotient` sends the class
of `f` to the normal form of `f`. -/
@[simp]
theorem IsGroebnerBasis.coe_restrictSupportEquivQuotient_symm_mk (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) (f : MvPolynomial σ R) :
    ((h.restrictSupportEquivQuotient hG).symm (Ideal.Quotient.mk I f) : MvPolynomial σ R) =
      h.normalForm hG f :=
  (rfl)

variable (h : m.IsGroebnerBasis G I) (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))

include h hG

/-- The normal form is supported on the standard monomials. -/
@[simp]
theorem IsGroebnerBasis.normalForm_mem_restrictSupport (f : MvPolynomial σ R) :
    h.normalForm hG f ∈ restrictSupport R (m.standardMonomials I) :=
  h.coe_restrictSupportEquivQuotient_symm_mk hG f ▸
    ((h.restrictSupportEquivQuotient hG).symm (Ideal.Quotient.mk I f)).2

/-- A polynomial and its normal form have the same image in the quotient. -/
@[simp]
theorem IsGroebnerBasis.mk_normalForm (f : MvPolynomial σ R) :
    Ideal.Quotient.mk I (h.normalForm hG f) = Ideal.Quotient.mk I f := by
  rw [← h.restrictSupportEquivQuotient_apply hG ⟨_, h.normalForm_mem_restrictSupport hG f⟩]
  exact (h.restrictSupportEquivQuotient hG).apply_symm_apply _

/-- A polynomial is congruent to its normal form modulo `I`. -/
@[simp]
theorem IsGroebnerBasis.sub_normalForm_mem (f : MvPolynomial σ R) : f - h.normalForm hG f ∈ I :=
  Ideal.Quotient.eq.1 (h.mk_normalForm hG f).symm

/-- **Characterization of the normal form.** The normal form of `f` is the unique polynomial
supported on the standard monomials of `I` that is congruent to `f` modulo `I`. -/
theorem IsGroebnerBasis.normalForm_eq_iff :
    h.normalForm hG f = r ↔ r ∈ restrictSupport R (m.standardMonomials I) ∧ f - r ∈ I := by
  refine ⟨fun hr ↦ hr ▸ ⟨h.normalForm_mem_restrictSupport hG f, h.sub_normalForm_mem hG f⟩,
    fun ⟨hr, hfr⟩ ↦ eq_of_sub_mem_of_mem_restrictSupport (h.normalForm_mem_restrictSupport hG f)
      hr ?_⟩
  simpa using I.sub_mem hfr (h.sub_normalForm_mem hG f)

/-- A polynomial supported on the standard monomials is its own normal form. -/
@[simp]
theorem IsGroebnerBasis.normalForm_of_mem_restrictSupport
    (hr : r ∈ restrictSupport R (m.standardMonomials I)) : h.normalForm hG r = r :=
  (h.normalForm_eq_iff hG).2 ⟨hr, by simp⟩

/-- The normal form is idempotent. -/
theorem IsGroebnerBasis.normalForm_normalForm (f : MvPolynomial σ R) :
    h.normalForm hG (h.normalForm hG f) = h.normalForm hG f :=
  h.normalForm_of_mem_restrictSupport hG (h.normalForm_mem_restrictSupport hG f)

/-- Two polynomials have the same normal form if and only if they are congruent modulo `I`. -/
theorem IsGroebnerBasis.normalForm_eq_normalForm_iff :
    h.normalForm hG f = h.normalForm hG g ↔ f - g ∈ I := by
  rw [← Ideal.Quotient.eq, ← h.mk_normalForm hG f, ← h.mk_normalForm hG g]
  refine ⟨fun hfg ↦ hfg ▸ rfl, fun hfg ↦ eq_of_sub_mem_of_mem_restrictSupport
    (h.normalForm_mem_restrictSupport hG f) (h.normalForm_mem_restrictSupport hG g)
    (Ideal.Quotient.eq.1 hfg)⟩

/-- **Ideal membership.** The normal form of `f` vanishes if and only if `f ∈ I`. -/
@[simp]
theorem IsGroebnerBasis.normalForm_eq_zero_iff : h.normalForm hG f = 0 ↔ f ∈ I := by
  simpa using h.normalForm_eq_normalForm_iff hG (g := 0)

/-- The kernel of the normal form is `I`. -/
@[simp]
theorem IsGroebnerBasis.ker_normalForm : LinearMap.ker (h.normalForm hG) = I.restrictScalars R :=
  Submodule.ext fun _ ↦ by
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, h.normalForm_eq_zero_iff hG]

/-- The range of the normal form consists of the polynomials supported on the standard monomials
of `I`. -/
@[simp]
theorem IsGroebnerBasis.range_normalForm :
    LinearMap.range (h.normalForm hG) = restrictSupport R (m.standardMonomials I) :=
  le_antisymm (by rintro _ ⟨f, rfl⟩; exact h.normalForm_mem_restrictSupport hG f)
    fun r hr ↦ ⟨r, h.normalForm_of_mem_restrictSupport hG hr⟩

/-- Reducing the left factor of a product to normal form does not change the normal form of the
product. -/
@[simp]
theorem IsGroebnerBasis.normalForm_normalForm_mul (f g : MvPolynomial σ R) :
    h.normalForm hG (h.normalForm hG f * g) = h.normalForm hG (f * g) :=
  (h.normalForm_eq_normalForm_iff hG).2 <| by
    rw [← sub_mul]
    exact I.mul_mem_right g (by simpa using I.neg_mem (h.sub_normalForm_mem hG f))

/-- Reducing the right factor of a product to normal form does not change the normal form of the
product. -/
@[simp]
theorem IsGroebnerBasis.normalForm_mul_normalForm (f g : MvPolynomial σ R) :
    h.normalForm hG (f * h.normalForm hG g) = h.normalForm hG (f * g) := by
  rw [mul_comm, normalForm_normalForm_mul, mul_comm]

/-- The coordinates of a class in the standard monomial basis are the coefficients of the normal
form of any representative. -/
@[simp]
theorem IsGroebnerBasis.basisQuotient_repr_mk (f : MvPolynomial σ R) (c : m.standardMonomials I) :
    (h.basisQuotient hG).repr (Ideal.Quotient.mk I f) c = (h.normalForm hG f).coeff c := by
  simp [basisQuotient]

/-- The remainders of `f` on division by a Gröbner basis of `I` whose nonzero members have unit
leading coefficients are exactly the normal form of `f`. -/
theorem IsGroebnerBasis.isRemainder_iff_eq_normalForm :
    m.IsRemainder f G r ↔ r = h.normalForm hG f := by
  have key {r : MvPolynomial σ R} (hr : m.IsRemainder f G r) : r = h.normalForm hG f :=
    ((h.normalForm_eq_iff hG).2 ⟨h.mem_restrictSupport_of_isRemainder hr,
      Ideal.span_le.2 h.subset hr.sub_mem_span⟩).symm
  refine ⟨key, ?_⟩
  rintro rfl
  obtain ⟨r, hr⟩ := exists_isRemainder hG f
  rwa [← key hr]

end CommRing

end MonomialOrder

end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.WeightedNormalForm -/
section

section
set_option autoImplicit false
set_option maxHeartbeats 200000

noncomputable section
namespace FourPapers.Sublattice
open Classical MvPolynomial
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R V : Type*} [CommRing R]

/-- Checking a polynomial linear map on its actual monomial expansion suffices
to prove a support or submodule bound. -/
lemma polynomialLinearMap_mem (T : MvPolynomial V R →ₗ[R] MvPolynomial V R)
    (Q : Submodule R (MvPolynomial V R)) (f : MvPolynomial V R)
    (h : ∀a∈f.support,T (monomial a 1)∈Q) : T f∈Q := by
  rw [f.as_sum,map_sum]
  apply Submodule.sum_mem
  intro a ha
  rw [show monomial a (f.coeff a) = f.coeff a • monomial a (1 : R) by
      simp only [smul_monomial, smul_eq_mul, mul_one],
    map_smul]
  exact Q.smul_mem _ (h a ha)

/-- An actual normal-form map with strictly decreasing monomial relations
preserves the filtration by any nonnegative integer rank. The proof is finite
strong induction on that rank, so no completion or convergence is assumed. -/
theorem normalizer_preserves_monomial_rank
    (T : MvPolynomial V R →ₗ[R] MvPolynomial V R)
    (P : (V →₀ ℕ) → Prop) (rank : (V →₀ ℕ) → ℕ)
    (hfix : ∀a,P a→T (monomial a 1)=monomial a 1)
    (hred : ∀a,¬P a→∃p : MvPolynomial V R,
      (∀b∈p.support,rank b<rank a) ∧ T (monomial a 1)=T p) :
    ∀a,T (monomial a 1)∈restrictSupport R {b | rank b≤rank a} := by
  have hh : ∀r : ℕ,∀a,rank a=r→
      T (monomial a 1)∈restrictSupport R {b | rank b≤rank a} := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro a har
      by_cases ha : P a
      · rw [hfix a ha]
        simp
      · obtain ⟨p,hp,he⟩ := hred a ha
        rw [he]
        apply polynomialLinearMap_mem T _ p
        intro b hb
        have hbr : rank b<r := by simpa [har] using hp b hb
        have hrec := ih (rank b) hbr b rfl
        rw [mem_restrictSupport_iff] at hrec ⊢
        intro c hc
        exact (hrec hc).trans (Nat.le_of_lt (hp b hb))
  exact fun a => hh (rank a) a rfl

/-- A nonstandard monomial has only strictly lower-rank terms in normal form. -/
theorem normalizer_strictly_lowers_monomial
    (T : MvPolynomial V R →ₗ[R] MvPolynomial V R)
    (P : (V →₀ ℕ) → Prop) (rank : (V →₀ ℕ) → ℕ)
    (hfix : ∀a,P a→T (monomial a 1)=monomial a 1)
    (hred : ∀a,¬P a→∃p : MvPolynomial V R,
      (∀b∈p.support,rank b<rank a) ∧ T (monomial a 1)=T p)
    (a : V →₀ ℕ) (ha : ¬P a) :
    T (monomial a 1)∈restrictSupport R {b | rank b<rank a} := by
  obtain ⟨p,hp,he⟩ := hred a ha
  rw [he]
  apply polynomialLinearMap_mem T _ p
  intro b hb
  have hrec := normalizer_preserves_monomial_rank T P rank hfix hred b
  rw [mem_restrictSupport_iff] at hrec ⊢
  intro c hc
  exact (hrec hc).trans_lt (hp b hb)

/-- The corresponding support bound for arbitrary polynomials, rather than
only basis monomials. -/
theorem normalizer_preserves_rank
    (T : MvPolynomial V R →ₗ[R] MvPolynomial V R)
    (P : (V →₀ ℕ) → Prop) (rank : (V →₀ ℕ) → ℕ)
    (hfix : ∀a,P a→T (monomial a 1)=monomial a 1)
    (hred : ∀a,¬P a→∃p : MvPolynomial V R,
      (∀b∈p.support,rank b<rank a) ∧ T (monomial a 1)=T p)
    (q : ℕ) (f : MvPolynomial V R)
    (hf : f∈restrictSupport R {a | rank a≤q}) :
    T f∈restrictSupport R {a | rank a≤q} := by
  apply polynomialLinearMap_mem T _ f
  intro a ha
  have hh := normalizer_preserves_monomial_rank T P rank hfix hred a
  rw [mem_restrictSupport_iff] at hf hh ⊢
  intro b hb
  exact (show rank b ≤ rank a from hh hb).trans (show rank a ≤ q from hf ha)

/-- Specialization to the genuine quotient normal form attached to an actual
monic/unit-leading Gröbner basis. The hypotheses concern literal ideal
relations, not a postulated associated-graded quotient. -/
theorem groebner_normalForm_strictly_lowers
    (m : MonomialOrder V) (J : Ideal (MvPolynomial V R))
    (G : Set (MvPolynomial V R)) (hG : m.IsGroebnerBasis G J)
    (hu : ∀g∈G,g≠0→IsUnit (m.leadingCoeff g))
    (rank : (V →₀ ℕ) → ℕ)
    (hred : ∀a,a∉m.standardMonomials J→∃p : MvPolynomial V R,
      (∀b∈p.support,rank b<rank a) ∧ monomial a 1-p∈J)
    (a : V →₀ ℕ) (ha : a∉m.standardMonomials J) :
    hG.normalForm hu (monomial a 1)∈restrictSupport R {b | rank b<rank a} := by
  apply normalizer_strictly_lowers_monomial (hG.normalForm hu)
    (fun a => a∈m.standardMonomials J) rank _ _ a ha
  · intro a ha
    apply hG.normalForm_of_mem_restrictSupport hu
    exact (monomial_mem_restrictSupport R).mpr (Or.inl ha)
  · intro a ha
    obtain ⟨p,hp,he⟩ := hred a ha
    exact ⟨p,hp,(hG.normalForm_eq_normalForm_iff hu).mpr he⟩

/-- Strictly lower tails of actual monic Gröbner generators supply every
decreasing monomial relation used above, including all monomial multiples. -/
lemma groebner_decreasing_monomial_relations
    (m : MonomialOrder V) (J : Ideal (MvPolynomial V R))
    (G : Set (MvPolynomial V R)) (hG : m.IsGroebnerBasis G J)
    (w : V → ℕ)
    (htail : ∀g∈G,g≠0→∀b∈(monomial (m.degree g) 1-g).support,
      Finsupp.weight w b<Finsupp.weight w (m.degree g))
    (a : V →₀ ℕ) (ha : a∉m.standardMonomials J) :
    ∃p : MvPolynomial V R,
      (∀b∈p.support,Finsupp.weight w b<Finsupp.weight w a) ∧
        monomial a 1-p∈J := by
  obtain ⟨g,hg,hg0,hga⟩ : ∃g∈G,g≠0 ∧ m.degree g≤a := by
    by_contra hn
    apply ha
    rw [hG.mem_standardMonomials_iff]
    intro g hg hg0 hga
    exact hn ⟨g,hg,hg0,hga⟩
  let q : MvPolynomial V R := monomial (a-m.degree g) 1
  refine ⟨q*(monomial (m.degree g) 1-g),?_,?_⟩
  · intro b hb
    obtain ⟨c,hc,t,ht,rfl⟩ := Finset.mem_add.mp (support_mul _ _ hb)
    have hc' : c=a-m.degree g :=
      Finset.mem_singleton.mp (support_monomial_subset hc)
    rw [hc',map_add]
    calc
      _ < Finsupp.weight w (a-m.degree g)+Finsupp.weight w (m.degree g) :=
        Nat.add_lt_add_left (htail g hg hg0 t ht) _
      _ = Finsupp.weight w a := by rw [←map_add,tsub_add_cancel_of_le hga]
  · have hmul : q*monomial (m.degree g) 1=monomial a 1 := by
      simp only [q,monomial_mul_monomial,one_mul,tsub_add_cancel_of_le hga]
    have he : monomial a 1-q*(monomial (m.degree g) 1-g)=q*g := by
      rw [mul_sub,hmul]
      abel
    rw [he]
    exact J.mul_mem_left q (hG.subset hg)

theorem groebner_normalForm_strictly_lowers_of_tails
    (m : MonomialOrder V) (J : Ideal (MvPolynomial V R))
    (G : Set (MvPolynomial V R)) (hG : m.IsGroebnerBasis G J)
    (hu : ∀g∈G,g≠0→IsUnit (m.leadingCoeff g)) (w : V → ℕ)
    (htail : ∀g∈G,g≠0→∀b∈(monomial (m.degree g) 1-g).support,
      Finsupp.weight w b<Finsupp.weight w (m.degree g))
    (a : V →₀ ℕ) (ha : a∉m.standardMonomials J) :
    hG.normalForm hu (monomial a 1)∈
      restrictSupport R {b | Finsupp.weight w b<Finsupp.weight w a} :=
  groebner_normalForm_strictly_lowers m J G hG hu (Finsupp.weight w)
    (groebner_decreasing_monomial_relations m J G hG w htail) a ha

/-- Actual normal forms preserve every grading for which the ideal is
homogeneous. This will be applied to the vertex grading and the row grading,
independently of the filtration used to form the initial ideal. -/
theorem groebner_normalForm_component {A : Type*} [AddCommMonoid A]
    (m : MonomialOrder V) (J : Ideal (MvPolynomial V R))
    (G : Set (MvPolynomial V R)) (hG : m.IsGroebnerBasis G J)
    (hu : ∀g∈G,g≠0→IsUnit (m.leadingCoeff g)) (deg : V → A)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule R deg))
    (a : A) (f : MvPolynomial V R) :
    hG.normalForm hu (weightedHomogeneousComponent deg a f)=
      weightedHomogeneousComponent deg a (hG.normalForm hu f) := by
  apply (hG.normalForm_eq_iff hu).mpr
  constructor
  · have hf := (mem_restrictSupport_iff R).mp (hG.normalForm_mem_restrictSupport hu f)
    rw [mem_restrictSupport_iff,support_weightedHomogeneousComponent,Finset.coe_filter]
    exact fun c hc => hf hc.1
  · rw [←map_sub]
    exact weightedHomogeneousComponent_mem_of_mem R deg hJ (hG.sub_normalForm_mem hu f) a

theorem groebner_normalForm_homogeneous {A : Type*} [AddCommMonoid A]
    (m : MonomialOrder V) (J : Ideal (MvPolynomial V R))
    (G : Set (MvPolynomial V R)) (hG : m.IsGroebnerBasis G J)
    (hu : ∀g∈G,g≠0→IsUnit (m.leadingCoeff g)) (deg : V → A)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule R deg))
    (a : A) (f : MvPolynomial V R) (hf : IsWeightedHomogeneous deg f a) :
    IsWeightedHomogeneous deg (hG.normalForm hu f) a := by
  rw [←weightedHomogeneousComponent_eq_self hf,
    groebner_normalForm_component m J G hG hu deg hJ]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GroebnerKoszulCoordinates -/
section

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory MvPolynomial CommAlg.Koszul CommAlg.Polymatroid
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u

private theorem groebnerEquiv_sum {R M N ι : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Fintype ι]
    (e : M ≃ₗ[R] N) (f : ι → M) : e (∑ j, f j) = ∑ j, e (f j) :=
  map_sum e.toAddEquiv f Finset.univ

variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]
variable (m : MonomialOrder V) (J : Ideal (MvPolynomial V k))
  (G : Set (MvPolynomial V k)) (hG : m.IsGroebnerBasis G J)
  (hu : ∀g∈G,g≠0→IsUnit (m.leadingCoeff g)) (B : Family V)
  (hstd : ∀a,a∈m.standardMonomials J ↔ QuotientAllowed B a)

/-- The standard monomial identification is an actual linear equivalence of
the monomial and binomial quotient rings, not an algebra isomorphism. -/
def groebnerCoefficientEquiv : CoefficientQuotient (k := k) B ≃ₗ[k]
    MvPolynomial V k ⧸ J :=
  (quotientMonomialBasis B).equiv (hG.basisQuotient hu)
    (Equiv.subtypeEquivRight (fun a => (hstd a).symm))

lemma groebnerCoefficientEquiv_basis (a : {a // QuotientAllowed B a}) :
    groebnerCoefficientEquiv m J G hG hu B hstd (quotientMonomialBasis B a)=
      Ideal.Quotient.mk J (monomial a.val 1) := by
  rw [groebnerCoefficientEquiv, Module.Basis.equiv_apply,
    MonomialOrder.IsGroebnerBasis.basisQuotient_apply]
  rfl

lemma groebnerCoefficientEquiv_symm_repr (f : MvPolynomial V k)
    (a : {a // QuotientAllowed B a}) :
    (quotientMonomialBasis B).repr
      ((groebnerCoefficientEquiv m J G hG hu B hstd).symm (Ideal.Quotient.mk J f)) a =
      (hG.normalForm hu f).coeff a.val := by
  let e : {a // QuotientAllowed B a} ≃ m.standardMonomials J :=
    Equiv.subtypeEquivRight (fun a => (hstd a).symm)
  change (quotientMonomialBasis B).repr
    ((quotientMonomialBasis B).repr.symm
      (((hG.basisQuotient hu).reindex e.symm).repr (Ideal.Quotient.mk J f))) a = _
  rw [LinearEquiv.apply_symm_apply, Module.Basis.repr_reindex_apply]
  exact hG.basisQuotient_repr_mk hu f (e a)

lemma groebnerCoefficientEquiv_symm_monomial {a : Exponent V}
    (ha : QuotientAllowed B a) :
    (groebnerCoefficientEquiv m J G hG hu B hstd).symm
      (Ideal.Quotient.mk J (monomial a 1))=quotientMonomial B a := by
  apply (groebnerCoefficientEquiv m J G hG hu B hstd).injective
  rw [LinearEquiv.apply_symm_apply]
  simpa only [quotientMonomialBasis_apply] using
    (groebnerCoefficientEquiv_basis m J G hG hu B hstd ⟨a,ha⟩).symm

/-- Apply the actual coefficient identification to every exterior coordinate. -/
def groebnerKoszulCoordinates (i : ℕ) :
    (Set.powersetCard V i →₀ CoefficientQuotient (k := k) B) ≃ₗ[k]
      (Set.powersetCard V i →₀ MvPolynomial V k ⧸ J) :=
  Finsupp.mapRange.linearEquiv (groebnerCoefficientEquiv m J G hG hu B hstd)

attribute [local irreducible] groebnerCoefficientEquiv

/-- The ordinary differential of the genuine Koszul complex of `S/J`,
transported through its standard monomial basis. -/
def groebnerQuotientDifferential (i : ℕ) :
    (Set.powersetCard V (i+1) →₀ CoefficientQuotient (k := k) B) →ₗ[k]
      (Set.powersetCard V i →₀ CoefficientQuotient (k := k) B) :=
  (groebnerKoszulCoordinates m J G hG hu B hstd i).symm.toLinearMap.comp
    (((coordinateDifferential (X : V → MvPolynomial V k)
      (ModuleCat.of (MvPolynomial V k) (MvPolynomial V k ⧸ J)) i).restrictScalars k).comp
      (groebnerKoszulCoordinates m J G hG hu B hstd (i+1)).toLinearMap)

lemma groebnerQuotientDifferential_comp (i : ℕ) :
    (groebnerQuotientDifferential m J G hG hu B hstd i).comp
      (groebnerQuotientDifferential m J G hG hu B hstd (i+1))=0 := by
  apply LinearMap.ext
  intro x
  simp only [groebnerQuotientDifferential, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearMap.restrictScalars_apply,
    LinearEquiv.apply_symm_apply, LinearMap.zero_apply]
  have hh := LinearMap.congr_fun (coordinateDifferential_comp
    (X : V → MvPolynomial V k)
    (ModuleCat.of (MvPolynomial V k) (MvPolynomial V k ⧸ J)) i)
      (groebnerKoszulCoordinates m J G hG hu B hstd (i+2) x)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hh
  rw [hh]
  exact (groebnerKoszulCoordinates m J G hG hu B hstd i).symm.map_zero

set_option backward.isDefEq.respectTransparency true in
/-- Literal matrix formula: multiply the standard monomial by the deleted
variable in `S/J`, then take its actual Gröbner normal form. -/
lemma groebnerQuotientDifferential_basis (i : ℕ) (t : QuotientIndex B (i+1)) :
    groebnerQuotientDifferential m J G hG hu B hstd i
      (quotientCoefficientBasis B (i+1) t) =
      ∑j : {j // j∈t.1.val},
        TauCeti.ExteriorAlgebra.basisEraseSign j.val t.1.val •
          Finsupp.single (eraseIndex t.1 j)
            ((groebnerCoefficientEquiv m J G hG hu B hstd).symm
              (Ideal.Quotient.mk J (monomial (t.2.val+Finsupp.single j.val 1) 1))) := by
  rcases t with ⟨s,a⟩
  rw [quotientCoefficientBasis_apply]
  simp only [groebnerQuotientDifferential,LinearMap.comp_apply,
    LinearEquiv.coe_coe,LinearMap.restrictScalars_apply,
    groebnerKoszulCoordinates,Finsupp.mapRange.linearEquiv_apply,
    Finsupp.mapRange_single]
  rw [show groebnerCoefficientEquiv m J G hG hu B hstd (quotientMonomial B a.val)=
      Ideal.Quotient.mk J (monomial a.val 1) by
        simpa only [quotientMonomialBasis_apply] using
          groebnerCoefficientEquiv_basis m J G hG hu B hstd a,
    coordinateDifferential_single]
  rw [groebnerEquiv_sum (R := k)
    (M := Set.powersetCard V i →₀ MvPolynomial V k ⧸ J)
    (N := Set.powersetCard V i →₀ CoefficientQuotient (k := k) B)
    (Finsupp.mapRange.linearEquiv (groebnerCoefficientEquiv m J G hG hu B hstd)).symm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [smul_comm (X j.val)]
  have hm : (X j.val : MvPolynomial V k) •
      Ideal.Quotient.mk J (monomial a.val 1) =
        Ideal.Quotient.mk J (monomial (a.val+Finsupp.single j.val 1) 1) := by
    change Ideal.Quotient.mk J (X j.val*monomial a.val (1 : k))=_
    simp [X,monomial_mul_monomial,add_comm]
  rw [hm]
  simp only [groebnerKoszulCoordinates, Finsupp.mapRange.linearEquiv_symm,
    Finsupp.mapRange.linearEquiv_apply, Finsupp.mapRange_single,
    map_zsmul_unit, Finsupp.smul_single]

private theorem groebnerEquiv_sub {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (x y : M) : e (x-y) = e x-e y :=
  map_sub e.toAddEquiv x y

private theorem groebnerEquiv_unit_smul {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (c : ℤˣ) (x : M) : e (c • x) = c • e x :=
  map_zsmul_unit e.toAddEquiv c x

lemma quotientCoefficientBasis_repr_single (i : ℕ) (s t : Set.powersetCard V i)
    (y : CoefficientQuotient (k := k) B) (a : {a // QuotientAllowed B a}) :
    (quotientCoefficientBasis B i).repr (Finsupp.single s y) ⟨t,a⟩=
      if s=t then (quotientMonomialBasis B).repr y a else 0 := by
  simp only [quotientCoefficientBasis, Finsupp.basis_repr, Finsupp.single_apply]
  by_cases h : s = t
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, (quotientMonomialBasis (k := k) B).repr.map_zero,
      Finsupp.zero_apply]

/-- The actual differential of `S/J` has the monomial quotient differential as
its leading-weight part. Every entry of their difference strictly decreases
the total coefficient-plus-exterior weight. -/
theorem groebnerQuotientDifferential_strictly_lowers (w : V → ℕ)
    (htail : ∀g∈G,g≠0→∀b∈(monomial (m.degree g) 1-g).support,
      Finsupp.weight w b<Finsupp.weight w (m.degree g))
    (i : ℕ) (t : QuotientIndex B (i+1)) (s : QuotientIndex B i)
    (hweight : Finsupp.weight w (quotientDegree t)≤
      Finsupp.weight w (quotientDegree s)) :
    (quotientCoefficientBasis (k := k) B i).repr
      ((groebnerQuotientDifferential m J G hG hu B hstd i-
        quotientDifferential (k := k) B i) (quotientCoefficientBasis (k := k) B (i+1) t)) s=0 := by
  rw [LinearMap.sub_apply,
    groebnerEquiv_sub (R := k) (quotientCoefficientBasis (k := k) B i).repr,
    Finsupp.sub_apply, sub_eq_zero, groebnerQuotientDifferential_basis,
    quotientDifferential_basis,
    groebnerEquiv_sum (R := k) (quotientCoefficientBasis (k := k) B i).repr,
    groebnerEquiv_sum (R := k) (quotientCoefficientBasis (k := k) B i).repr,
    Finsupp.finsetSum_apply, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases ha : QuotientAllowed B (t.2.val+Finsupp.single j.val 1)
  · rw [dif_pos ha,groebnerCoefficientEquiv_symm_monomial m J G hG hu B hstd ha]
    rw [quotientCoefficientBasis_apply]
    rfl
  · rw [dif_neg ha, (quotientCoefficientBasis (k := k) B i).repr.map_zero,
      Finsupp.zero_apply,
      groebnerEquiv_unit_smul (R := k) (quotientCoefficientBasis (k := k) B i).repr,
      Finsupp.smul_apply]
    have hn : t.2.val+Finsupp.single j.val 1∉m.standardMonomials J :=
      fun hh => ha ((hstd _).mp hh)
    have hnf := groebner_normalForm_strictly_lowers_of_tails m J G hG hu w htail
      (t.2.val+Finsupp.single j.val 1) hn
    rw [quotientCoefficientBasis_repr_single]
    by_cases hs : eraseIndex t.1 j=s.1
    · rw [if_pos hs,groebnerCoefficientEquiv_symm_repr]
      have hzero : (hG.normalForm hu (monomial
          (t.2.val+Finsupp.single j.val 1) 1)).coeff s.2.val=0 := by
        by_contra hc
        have hlt := (mem_restrictSupport_iff k).mp hnf
          (mem_support_iff.mpr hc)
        change Finsupp.weight w s.2.val <
          Finsupp.weight w (t.2.val+Finsupp.single j.val 1) at hlt
        have he : (t.2.val+Finsupp.single j.val 1)+faceExponent s.1.val=
            quotientDegree t := by
          rw [←hs]
          change (t.2.val+Finsupp.single j.val 1)+
            faceExponent (t.1.val.erase j.val)=t.2.val+faceExponent t.1.val
          rw [add_assoc,add_comm (Finsupp.single j.val 1),faceExponent_erase_add j.property]
        have hw := congrArg (Finsupp.weight w) he
        simp only [map_add,quotientDegree] at hlt hw hweight
        omega
      rw [hzero,smul_zero]
    · rw [if_neg hs,smul_zero]

theorem groebnerQuotientDifferential_basis_homogeneous
    {A : Type*} [AddCommMonoid A] (deg : V → A)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule k deg))
    (i : ℕ) (t : QuotientIndex B (i+1)) :
    groebnerQuotientDifferential m J G hG hu B hstd i
      (quotientCoefficientBasis B (i+1) t)∈
      CommAlg.Grading.Piece (quotientCoefficientBasis (k := k) B i)
        (fun s => Finsupp.weight deg (quotientDegree s))
        (Finsupp.weight deg (quotientDegree t)) := by
  rw [groebnerQuotientDifferential_basis]
  apply Submodule.sum_mem
  intro j hj
  apply (Submodule.smul_mem_iff' _ (TauCeti.ExteriorAlgebra.basisEraseSign j.val t.1.val)).mpr
  rw [CommAlg.Grading.mem_piece]
  intro s hs
  rw [quotientCoefficientBasis_repr_single] at hs
  split_ifs at hs with hface
  · rw [groebnerCoefficientEquiv_symm_repr] at hs
    have hnf := groebner_normalForm_homogeneous m J G hG hu deg hJ
      (Finsupp.weight deg (t.2.val+Finsupp.single j.val 1))
      (monomial (t.2.val+Finsupp.single j.val 1) 1)
      (isWeightedHomogeneous_monomial deg _ _ rfl)
    have ha := hnf hs
    change Finsupp.weight deg (s.2.val+faceExponent s.1.val)=_
    rw [map_add,ha,←map_add,←hface]
    change Finsupp.weight deg ((t.2.val+Finsupp.single j.val 1)+
      faceExponent (t.1.val.erase j.val))=
      Finsupp.weight deg (t.2.val+faceExponent t.1.val)
    rw [add_assoc,add_comm (Finsupp.single j.val 1),faceExponent_erase_add j.property]
  · exact (hs rfl).elim

/-- Any actual polynomial grading of `J` is preserved by the transported
ordinary Koszul differential, including simultaneous vertex and row degrees. -/
theorem groebnerQuotientDifferential_homogeneous
    {A : Type*} [AddCommMonoid A] (deg : V → A)
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule k deg))
    (a : A) (i : ℕ)
    (x : Set.powersetCard V (i+1) →₀ CoefficientQuotient (k := k) B)
    (hx : x∈CommAlg.Grading.Piece (quotientCoefficientBasis B (i+1))
      (fun s => Finsupp.weight deg (quotientDegree s)) a) :
    groebnerQuotientDifferential m J G hG hu B hstd i x∈
      CommAlg.Grading.Piece (quotientCoefficientBasis B i)
        (fun s => Finsupp.weight deg (quotientDegree s)) a := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t,ht,rfl⟩ := hx
    change Finsupp.weight deg (quotientDegree t) = a at ht
    simpa only [ht] using groebnerQuotientDifferential_basis_homogeneous
      m J G hG hu B hstd deg hJ i t
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientPreviousDifferential -/
section

/-! The outgoing differential of the actual quotient Koszul complex, including degree zero. -/
section
set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

def quotientPreviousDifferential (B : Family V) : ∀ p : ℕ,
    (Set.powersetCard V p →₀ CoefficientQuotient (k := k) B) →ₗ[k]
      (Set.powersetCard V p.pred →₀ CoefficientQuotient (k := k) B)
  | 0 => 0
  | p+1 => quotientDifferential (k := k) B p

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GraphPreparation -/
section
section
set_option Elab.async false


/- SOURCE FourPapers.Sublattice.GraphColons -/
section ExtensionSource0

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

/-!
# Interval-labelled graph predecessor colons

This is the literal two-row instance of the paper's coefficient ideals. The
interval hypothesis will be obtained from a closed graph by ordering each
connected component. No Betti assertion is assumed here.
-/

noncomputable section
namespace FourPapers.Sublattice
open Classical Finset CommAlg.Polymatroid
universe u
variable {N : ℕ}
abbrev GraphRows (N : ℕ) : Fin 2 → ℕ := fun _ => N

/-- Every edge spans the whole interval between its endpoints. -/
def IntervalLabeling (G : SimpleGraph (Fin N)) : Prop :=
  ∀ i j k, i<j → j<k → G.Adj i k → G.Adj i j ∧ G.Adj j k

lemma interval_adj_left {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G)
    {i j k : Fin N} (hik : G.Adj i k) (hij : i≤j) (hjk : j<k) : G.Adj j k := by
  rcases hij.eq_or_lt with rfl | hij
  · exact hik
  · exact (hG i j k hij hjk hik).2

lemma interval_adj_right {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G)
    {i j k : Fin N} (hik : G.Adj i k) (hij : i<j) (hjk : j≤k) : G.Adj i j := by
  rcases hjk.eq_or_lt with rfl | hjk
  · exact hik
  · exact (hG i j k hij hjk hik).1

def graphTuple (i j : Fin N) : FiniteTuple (GraphRows N) :=
  fun r => if r=0 then i else j
@[simp] lemma graphTuple_zero (i j : Fin N) : graphTuple i j 0=i := by simp [graphTuple]
@[simp] lemma graphTuple_one (i j : Fin N) : graphTuple i j 1=j := by simp [graphTuple]

lemma graphTuple_eta (a : FiniteTuple (GraphRows N)) : graphTuple (a 0) (a 1)=a := by
  funext r
  fin_cases r <;> simp

def graphEdgeLattice (G : SimpleGraph (Fin N)) : Finset (FiniteTuple (GraphRows N)) :=
  univ.filter (fun a => a 0<a 1 ∧ G.Adj (a 0) (a 1))

@[simp] lemma mem_graphEdgeLattice (G : SimpleGraph (Fin N)) (a : FiniteTuple (GraphRows N)) :
    a∈graphEdgeLattice G ↔ a 0<a 1 ∧ G.Adj (a 0) (a 1) := by simp [graphEdgeLattice]

/-- The edge pairs form the precise sublattice used by the all-powers theorem. -/
theorem graphEdgeLattice_closed {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G) :
    finiteLatticeClosed (GraphRows N) (graphEdgeLattice G) := by
  constructor
  · intro a ha b hb
    rcases (mem_graphEdgeLattice G a).mp ha with ⟨ha,haG⟩
    rcases (mem_graphEdgeLattice G b).mp hb with ⟨hb,hbG⟩
    apply (mem_graphEdgeLattice G (a⊓b)).mpr
    change min (a 0) (b 0) < min (a 1) (b 1) ∧
      G.Adj (min (a 0) (b 0)) (min (a 1) (b 1))
    refine ⟨min_lt_min ha hb,?_⟩
    by_cases h0 : a 0≤b 0 <;> by_cases h1 : a 1≤b 1
    · simpa [min_eq_left h0,min_eq_left h1] using haG
    · have h10 : b 1≤a 1 := (lt_of_not_ge h1).le
      simpa [min_eq_left h0,min_eq_right h10] using
        interval_adj_right hG haG (h0.trans_lt hb) h10
    · have h00 : b 0≤a 0 := (lt_of_not_ge h0).le
      simpa [min_eq_right h00,min_eq_left h1] using
        interval_adj_right hG hbG (h00.trans_lt ha) h1
    · simpa [min_eq_right (le_of_not_ge h0),min_eq_right (le_of_not_ge h1)] using hbG
  · intro a ha b hb
    rcases (mem_graphEdgeLattice G a).mp ha with ⟨ha,haG⟩
    rcases (mem_graphEdgeLattice G b).mp hb with ⟨hb,hbG⟩
    apply (mem_graphEdgeLattice G (a⊔b)).mpr
    change max (a 0) (b 0) < max (a 1) (b 1) ∧
      G.Adj (max (a 0) (b 0)) (max (a 1) (b 1))
    refine ⟨max_lt_max ha hb,?_⟩
    by_cases h0 : a 0≤b 0 <;> by_cases h1 : a 1≤b 1
    · simpa [max_eq_right h0,max_eq_right h1] using hbG
    · have h10 : b 1≤a 1 := (lt_of_not_ge h1).le
      simpa [max_eq_right h0,max_eq_left h10] using
        interval_adj_left hG haG h0 (hb.trans_le h10)
    · have h00 : b 0≤a 0 := (lt_of_not_ge h0).le
      simpa [max_eq_left h00,max_eq_right h1] using
        interval_adj_left hG hbG h00 (ha.trans_le h1)
    · simpa [max_eq_left (le_of_not_ge h0),max_eq_left (le_of_not_ge h1)] using haG

/-- The variables in the linear part of the predecessor colon, with no choice
of a minimum-neighbour function required in its definition. -/
def graphLinearVariables (G : SimpleGraph (Fin N)) (a : FiniteTuple (GraphRows N)) :
    Finset (FiniteVariable.{u} (GraphRows N)) :=
  univ.filter (fun v =>
    (v.1=0 ∧ v.2.down<a 0 ∧ G.Adj v.2.down (a 1)) ∨
    (v.1=1 ∧ a 0<v.2.down ∧ v.2.down<a 1))

def graphResidualEdges (G : SimpleGraph (Fin N)) (a : FiniteTuple (GraphRows N)) :
    Finset (FiniteTuple (GraphRows N)) :=
  (graphEdgeLattice G).filter (fun b => ¬G.Adj (b 0) (a 1) ∧ b 1≤a 0)

def graphColonFamily (G : SimpleGraph (Fin N)) (a : FiniteTuple (GraphRows N)) :
    Family (FiniteVariable.{u} (GraphRows N)) :=
  (graphLinearVariables G a).image (fun v => Finsupp.single v 1) ∪
    finiteRowFamily (GraphRows N) (graphResidualEdges G a)

lemma graphRatio_single_x (a : FiniteTuple (GraphRows N)) (h : Fin N) (hh : h≠a 0) :
    finiteRowExponent (GraphRows N) (graphTuple h (a 1))-
      finiteRowExponent (GraphRows N) a = Finsupp.single ⟨0,ULift.up h⟩ 1 := by
  ext v
  rcases v with ⟨r,⟨j⟩⟩
  fin_cases r <;> by_cases hj : h=j
  all_goals simp [Finsupp.tsub_apply,finiteRowExponent_apply,Finsupp.single_apply,hj,hh,Ne.symm hh]
  all_goals subst j; simp [hh,Ne.symm hh]

lemma graphRatio_single_y (a : FiniteTuple (GraphRows N)) (h : Fin N) (hh : h≠a 1) :
    finiteRowExponent (GraphRows N) (graphTuple (a 0) h)-
      finiteRowExponent (GraphRows N) a = Finsupp.single ⟨1,ULift.up h⟩ 1 := by
  ext v
  rcases v with ⟨r,⟨j⟩⟩
  fin_cases r <;> by_cases hj : h=j
  all_goals simp [Finsupp.tsub_apply,finiteRowExponent_apply,Finsupp.single_apply,hj,hh,Ne.symm hh]
  all_goals subst j; simp [hh,Ne.symm hh]

lemma graphRatio_disjoint (a b : FiniteTuple (GraphRows N))
    (h0 : b 0≠a 0) (h1 : b 1≠a 1) :
    finiteRowExponent (GraphRows N) b-finiteRowExponent (GraphRows N) a =
      finiteRowExponent (GraphRows N) b := by
  ext v
  rcases v with ⟨r,⟨j⟩⟩
  fin_cases r
  · simp only [Finsupp.tsub_apply,finiteRowExponent_apply]
    by_cases hb : b 0=j
    · subst j; simp [h0,Ne.symm h0]
    · simp [hb]
  · simp only [Finsupp.tsub_apply,finiteRowExponent_apply]
    by_cases hb : b 1=j
    · subst j; simp [h1,Ne.symm h1]
    · simp [hb]

lemma graphRatio_contains_coordinate (a b : FiniteTuple (GraphRows N))
    (r : Fin 2) (hr : b r≠a r) :
    Finsupp.single (⟨r,ULift.up (b r)⟩ : FiniteVariable.{u} (GraphRows N)) 1 ≤
      finiteRowExponent (GraphRows N) b-finiteRowExponent (GraphRows N) a := by
  apply Finsupp.single_le_iff.mpr
  simp [Finsupp.tsub_apply,finiteRowExponent_apply,hr,Ne.symm hr]

/-- The residual is a literal variable restriction: its first-row variables
avoid the last vertex's neighbours, and its second row ends at the first vertex. -/
lemma graphResidualEdges_variable_restriction (G : SimpleGraph (Fin N))
    (a b : FiniteTuple (GraphRows N)) :
    b∈graphResidualEdges G a ↔
      b∈graphEdgeLattice G ∧ ¬G.Adj (b 0) (a 1) ∧ b 1≤a 0 := by
  simp [graphResidualEdges]

lemma graphResidualEdges_strict_predecessor (G : SimpleGraph (Fin N))
    {a b : FiniteTuple (GraphRows N)} (ha : a∈graphEdgeLattice G)
    (hb : b∈graphResidualEdges G a) : b≤a ∧ b≠a := by
  rcases (mem_graphEdgeLattice G a).mp ha with ⟨ha,_⟩
  rcases (graphResidualEdges_variable_restriction G a b).mp hb with ⟨hb,_,hbi⟩
  have hb01 := ((mem_graphEdgeLattice G b).mp hb).1
  constructor
  · intro r
    fin_cases r
    · exact (hb01.trans_le hbi).le
    · exact hbi.trans ha.le
  · intro he
    subst b
    exact (not_le_of_gt ha) hbi

/-- Residual generators nest along comparable edge pairs, exactly as used in
coefficient-quotient recursion. -/
lemma graphResidualEdges_mono {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G)
    {a b : FiniteTuple (GraphRows N)} (ha : a∈graphEdgeLattice G)
    (hb : b∈graphEdgeLattice G) (hab : a≤b) :
    graphResidualEdges G a ⊆ graphResidualEdges G b := by
  intro c hc
  rcases (graphResidualEdges_variable_restriction G a c).mp hc with ⟨hcG,hca,hci⟩
  apply (graphResidualEdges_variable_restriction G b c).mpr
  refine ⟨hcG,?_,hci.trans (hab 0)⟩
  intro hcb
  apply hca
  exact interval_adj_right hG hcb
    ((((mem_graphEdgeLattice G c).mp hcG).1.trans_le hci).trans
      ((mem_graphEdgeLattice G a).mp ha).1) (hab 1)


lemma graphLinearVariables_mem_x (G : SimpleGraph (Fin N))
    (a : FiniteTuple (GraphRows N)) (h : Fin N) :
    (⟨0,ULift.up h⟩ : FiniteVariable.{u} (GraphRows N))∈graphLinearVariables G a ↔
      h<a 0 ∧ G.Adj h (a 1) := by simp [graphLinearVariables]

lemma graphLinearVariables_mem_y (G : SimpleGraph (Fin N))
    (a : FiniteTuple (GraphRows N)) (h : Fin N) :
    (⟨1,ULift.up h⟩ : FiniteVariable.{u} (GraphRows N))∈graphLinearVariables G a ↔
      a 0<h ∧ h<a 1 := by simp [graphLinearVariables]

/-- Coordinate predecessor ratios generate exactly the disjoint linear and
residual parts. The proof treats every ratio; no linear-quotient assumption is used. -/
theorem graphCoordinateColon_contains_iff {G : SimpleGraph (Fin N)}
    (hG : IntervalLabeling G) {a : FiniteTuple (GraphRows N)}
    (ha : a∈graphEdgeLattice G) (α : Exponent (FiniteVariable.{u} (GraphRows N))) :
    Contains (finiteCoordinatePredecessorFamily (graphEdgeLattice G) a) α ↔
      Contains (graphColonFamily G a) α := by
  have ha01 := ((mem_graphEdgeLattice G a).mp ha).1
  have haG := ((mem_graphEdgeLattice G a).mp ha).2
  constructor
  · rintro ⟨v,hv,hvα⟩
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hv
    obtain ⟨hbE,hba,hne⟩ := mem_filter.mp hb
    have hb01 := ((mem_graphEdgeLattice G b).mp hbE).1
    have hbG := ((mem_graphEdgeLattice G b).mp hbE).2
    by_cases h0 : b 0=a 0
    · have h1 : b 1<a 1 := lt_of_le_of_ne (hba 1) (by
        intro h1
        apply hne
        funext r
        fin_cases r <;> assumption)
      have hb0 : graphTuple (a 0) (b 1)=b := by rw [← h0]; exact graphTuple_eta b
      have hr : finiteRowExponent (GraphRows N) b-finiteRowExponent (GraphRows N) a =
          Finsupp.single ⟨1,ULift.up (b 1)⟩ 1 := by
        simpa only [hb0] using graphRatio_single_y a (b 1) h1.ne
      refine ⟨Finsupp.single ⟨1,ULift.up (b 1)⟩ 1,?_,hr ▸ hvα⟩
      apply mem_union_left
      apply mem_image.mpr
      refine ⟨⟨1,ULift.up (b 1)⟩,?_,rfl⟩
      exact (graphLinearVariables_mem_y G a (b 1)).mpr ⟨h0 ▸ hb01,h1⟩
    · have h0lt : b 0<a 0 := lt_of_le_of_ne (hba 0) h0
      by_cases hbj : G.Adj (b 0) (a 1)
      · refine ⟨Finsupp.single ⟨0,ULift.up (b 0)⟩ 1,?_,
          (graphRatio_contains_coordinate a b 0 h0).trans hvα⟩
        apply mem_union_left
        exact mem_image.mpr ⟨⟨0,ULift.up (b 0)⟩,
          (graphLinearVariables_mem_x G a (b 0)).mpr ⟨h0lt,hbj⟩,rfl⟩
      · by_cases hbi : a 0<b 1
        · have h1lt : b 1<a 1 := lt_of_le_of_ne (hba 1) (by
            intro h
            exact hbj (h ▸ hbG))
          refine ⟨Finsupp.single ⟨1,ULift.up (b 1)⟩ 1,?_,
            (graphRatio_contains_coordinate a b 1 h1lt.ne).trans hvα⟩
          apply mem_union_left
          exact mem_image.mpr ⟨⟨1,ULift.up (b 1)⟩,
            (graphLinearVariables_mem_y G a (b 1)).mpr ⟨hbi,h1lt⟩,rfl⟩
        · have hbi' : b 1≤a 0 := le_of_not_gt hbi
          have h1 : b 1≠a 1 := (hbi'.trans_lt ha01).ne
          refine ⟨finiteRowExponent (GraphRows N) b,?_,?_⟩
          · apply mem_union_right
            exact mem_image.mpr ⟨b,(graphResidualEdges_variable_restriction G a b).mpr
              ⟨hbE,hbj,hbi'⟩,rfl⟩
          · rwa [graphRatio_disjoint a b h0 h1] at hvα
  · rintro ⟨v,hv,hvα⟩
    rcases mem_union.mp hv with hv | hv
    · obtain ⟨e,he,hve⟩ := mem_image.mp hv
      subst v
      rcases e with ⟨r,⟨j⟩⟩
      fin_cases r
      · obtain ⟨hji,hjG⟩ := (graphLinearVariables_mem_x G a j).mp he
        let b := graphTuple j (a 1)
        refine ⟨finiteRowExponent (GraphRows N) b-finiteRowExponent (GraphRows N) a,?_,?_⟩
        · apply mem_image.mpr
          refine ⟨b,mem_filter.mpr ⟨?_,?_,?_⟩,rfl⟩
          · exact (mem_graphEdgeLattice G b).mpr ⟨hji.trans ha01,hjG⟩
          · intro s; fin_cases s <;> simp [b,hji.le]
          · intro h
            have := congrFun h 0
            exact hji.ne (by simpa [b] using this)
        · rwa [graphRatio_single_x a j hji.ne]
      · obtain ⟨hij,hjj⟩ := (graphLinearVariables_mem_y G a j).mp he
        let b := graphTuple (a 0) j
        refine ⟨finiteRowExponent (GraphRows N) b-finiteRowExponent (GraphRows N) a,?_,?_⟩
        · apply mem_image.mpr
          refine ⟨b,mem_filter.mpr ⟨?_,?_,?_⟩,rfl⟩
          · exact (mem_graphEdgeLattice G b).mpr
              ⟨hij,interval_adj_right hG haG hij hjj.le⟩
          · intro s; fin_cases s <;> simp [b,hjj.le]
          · intro h
            have := congrFun h 1
            exact hjj.ne (by simpa [b] using this)
        · rwa [graphRatio_single_y a j hjj.ne]
    · obtain ⟨b,hb,rfl⟩ := mem_image.mp hv
      have hbP := graphResidualEdges_strict_predecessor G ha hb
      have hbR := (graphResidualEdges_variable_restriction G a b).mp hb
      have hb01 := ((mem_graphEdgeLattice G b).mp hbR.1).1
      have h0 : b 0≠a 0 := (hb01.trans_le hbR.2.2).ne
      have h1 : b 1≠a 1 := (hbR.2.2.trans_lt ha01).ne
      refine ⟨finiteRowExponent (GraphRows N) b-finiteRowExponent (GraphRows N) a,?_,?_⟩
      · exact mem_image.mpr ⟨b,mem_filter.mpr ⟨hbR.1,hbP.1,hbP.2⟩,rfl⟩
      · rwa [graphRatio_disjoint a b h0 h1]

/-- Exact equality with the paper's genuine lexicographic predecessor colon. -/
theorem graphPredecessorColon_eq {k : Type*} [CommSemiring k]
    {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G)
    {a : FiniteTuple (GraphRows N)} (ha : a∈graphEdgeLattice G) :
    finitePredecessorColon (GraphRows N) (k := k) (graphEdgeLattice G) a =
      monomialIdeal k (graphColonFamily G a) := by
  rw [← finiteCoordinatePredecessor_ideal (k := k) (graphEdgeLattice_closed hG) ha]
  ext f
  simp_rw [mem_monomialIdeal_iff,graphCoordinateColon_contains_iff hG ha]

/-- The residual ideal omits every variable generating the linear factor. -/
theorem graphColon_disjoint_support (G : SimpleGraph (Fin N))
    {a : FiniteTuple (GraphRows N)} {v : FiniteVariable.{u} (GraphRows N)}
    (hv : v∈graphLinearVariables G a) {b : FiniteTuple (GraphRows N)}
    (hb : b∈graphResidualEdges G a) : finiteRowExponent (GraphRows N) b v=0 := by
  have hbR := (graphResidualEdges_variable_restriction G a b).mp hb
  rcases v with ⟨r,⟨j⟩⟩
  fin_cases r
  · obtain ⟨_,hjG⟩ := (graphLinearVariables_mem_x G a j).mp hv
    have hbj : b 0≠j := fun h => hbR.2.1 (h.symm ▸ hjG)
    simp [finiteRowExponent_apply,hbj]
  · obtain ⟨hij,_⟩ := (graphLinearVariables_mem_y G a j).mp hv
    have hbj : b 1≠j := (hbR.2.2.trans_lt hij).ne
    simp [finiteRowExponent_apply,hbj]

end FourPapers.Sublattice

end
end ExtensionSource0


/- SOURCE FourPapers.Sublattice.FiniteRowRestriction -/
section ExtensionSource1

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

noncomputable section
namespace FourPapers.Sublattice
open Classical Finset CommAlg.Polymatroid
universe u
variable {d : ℕ} {n : Fin d → ℕ}

/-- Literal restriction of a finite row family to a chosen set in each row. -/
def finiteRowRestriction (E : Finset (FiniteTuple n))
    (A : ∀r, Finset (Fin (n r))) : Finset (FiniteTuple n) :=
  E.filter (fun a => ∀r, a r∈A r)

@[simp] lemma mem_finiteRowRestriction (E : Finset (FiniteTuple n))
    (A : ∀r, Finset (Fin (n r))) (a : FiniteTuple n) :
    a∈finiteRowRestriction E A ↔ a∈E ∧ ∀r, a r∈A r := by
  simp [finiteRowRestriction]

lemma finiteRowRestriction_closed {E : Finset (FiniteTuple n)}
    (hE : finiteLatticeClosed n E) (A : ∀r, Finset (Fin (n r))) :
    finiteLatticeClosed n (finiteRowRestriction E A) := by
  constructor
  · intro a ha b hb
    obtain ⟨haE,haA⟩ := (mem_finiteRowRestriction E A a).mp ha
    obtain ⟨hbE,hbA⟩ := (mem_finiteRowRestriction E A b).mp hb
    apply (mem_finiteRowRestriction E A (a⊓b)).mpr
    refine ⟨hE.1 a haE b hbE,?_⟩
    intro r
    change min (a r) (b r)∈A r
    rcases le_total (a r) (b r) with h | h
    · simpa [min_eq_left h] using haA r
    · simpa [min_eq_right h] using hbA r
  · intro a ha b hb
    obtain ⟨haE,haA⟩ := (mem_finiteRowRestriction E A a).mp ha
    obtain ⟨hbE,hbA⟩ := (mem_finiteRowRestriction E A b).mp hb
    apply (mem_finiteRowRestriction E A (a⊔b)).mpr
    refine ⟨hE.2 a haE b hbE,?_⟩
    intro r
    change max (a r) (b r)∈A r
    rcases le_total (a r) (b r) with h | h
    · simpa [max_eq_right h] using hbA r
    · simpa [max_eq_left h] using haA r

/-- Fine-degree support lies in the selected row variables. -/
def SupportedRows (A : ∀r, Finset (Fin (n r)))
    (α : Exponent (FiniteVariable.{u} n)) : Prop :=
  ∀r j, 0<α ⟨r,ULift.up j⟩ → j∈A r

lemma SupportedRows.mono {A : ∀r, Finset (Fin (n r))}
    {α β : Exponent (FiniteVariable.{u} n)} (hα : SupportedRows A α)
    (hβα : β≤α) : SupportedRows A β := by
  intro r j hj
  exact hα r j (hj.trans_le (hβα _))

/-- In a supported fine degree, restricting the generators does not alter the
predecessor colon. A witness ratio forces every changed coordinate to remain
inside the selected rows; unchanged coordinates come from the retained facet. -/
theorem restrictedCoordinatePredecessor_contains_iff
    (E : Finset (FiniteTuple n)) (A : ∀r, Finset (Fin (n r)))
    {a : FiniteTuple n} (ha : a∈finiteRowRestriction E A)
    (α : Exponent (FiniteVariable.{u} n)) (hα : SupportedRows A α) :
    Contains (finiteCoordinatePredecessorFamily (finiteRowRestriction E A) a) α ↔
      Contains (finiteCoordinatePredecessorFamily E a) α := by
  constructor
  · rintro ⟨v,hv,hvα⟩
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hv
    obtain ⟨hbE,hba,hne⟩ := mem_filter.mp hb
    exact ⟨_,mem_image.mpr ⟨b,mem_filter.mpr
      ⟨((mem_finiteRowRestriction E A b).mp hbE).1,hba,hne⟩,rfl⟩,hvα⟩
  · rintro ⟨v,hv,hvα⟩
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hv
    obtain ⟨hbE,hba,hne⟩ := mem_filter.mp hb
    have haA := ((mem_finiteRowRestriction E A a).mp ha).2
    have hbA : ∀r, b r∈A r := by
      intro r
      by_cases h : b r=a r
      · rw [h]
        exact haA r
      · apply hα r (b r)
        have hh := hvα ⟨r,ULift.up (b r)⟩
        simp only [Finsupp.tsub_apply,finiteRowExponent_apply,ite_true,
          if_neg (Ne.symm h),Nat.sub_zero] at hh
        exact hh
    exact ⟨_,mem_image.mpr ⟨b,mem_filter.mpr
      ⟨(mem_finiteRowRestriction E A b).mpr ⟨hbE,hbA⟩,hba,hne⟩,rfl⟩,hvα⟩

end FourPapers.Sublattice

end
end ExtensionSource1


/- SOURCE FourPapers.Sublattice.ConnectingCycles -/
section ExtensionSource2

set_option autoImplicit false
set_option maxHeartbeats 200000

/-!
# Cycle spanning through an acyclic ambient complex

This is the elementary connecting-map argument for an ideal inside a polynomial
Koszul strand. The ambient contraction is explicit; the complementary projection
represents the quotient complex, and all boundaries in the conclusion are actual
differential images.
-/

noncomputable section
namespace FourPapers.Sublattice
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

lemma span_fixed_by_projection (q : Module.End R M) (G : Set M)
    (hG : ∀x∈G, q x=x) {x : M} (hx : x∈Submodule.span R G) : q x=x := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hG x hx
  | zero => exact map_zero q
  | add x y hx hy ihx ihy => rw [map_add,ihx,ihy]
  | smul c x hx ih => rw [map_smul,ih]

/-- If the connecting images of a specified set span every ideal cycle modulo
ideal boundaries, then the specified quotient cycles span modulo quotient
boundaries. This form uses an explicit projection and ambient contraction, so no
long-exact-sequence theorem or assumed homological surjectivity is hidden. -/
theorem quotientCycle_mem_span_of_connecting
    (d q h : Module.End R M)
    (hq : q.comp q=q) (hqd : q.comp (d.comp q)=q.comp d)
    (hh : d.comp h+h.comp d=LinearMap.id)
    (G : Set M) (hG : ∀x∈G, q x=x)
    (z : M) (hqz : q z=z)
    (hz : d z ∈ (Submodule.span R G ⊔ LinearMap.ker q).map d) :
    z ∈ Submodule.span R G ⊔ LinearMap.range (q.comp (d.comp q)) := by
  obtain ⟨w,hw,hwz⟩ := hz
  obtain ⟨g,hg,i,hi,hgi⟩ := Submodule.mem_sup.mp hw
  have hqg : q g=g := span_fixed_by_projection q G hG hg
  have hqi : q i=0 := hi
  have hdz : d z=d g+d i := by
    rw [←hwz,←hgi,map_add]
  have hcycle : d (z-g-i)=0 := by
    rw [map_sub,map_sub,hdz]
    abel
  have hfill : d (h (z-g-i))=z-g-i := by
    have he := LinearMap.congr_fun hh (z-g-i)
    change d (h (z-g-i))+h (d (z-g-i))=z-g-i at he
    simpa only [hcycle,map_zero,add_zero] using he
  have hproj : q (d (q (h (z-g-i))))=z-g := by
    have hqd' := LinearMap.congr_fun hqd (h (z-g-i))
    change q (d (q (h (z-g-i))))=q (d (h (z-g-i))) at hqd'
    rw [hqd',hfill,map_sub,map_sub,hqz,hqg,hqi,sub_zero]
  apply Submodule.mem_sup.mpr
  refine ⟨g,hg,z-g,?_,?_⟩
  · exact ⟨h (z-g-i),hproj⟩
  · abel

/-- Concrete useful reformulation of the connecting-image hypothesis. -/
lemma connecting_span_boundaries (d : Module.End R M) (G : Set M) (I : Submodule R M) :
    (Submodule.span R G ⊔ I).map d =
      Submodule.span R (d '' G) ⊔ I.map d := by
  rw [Submodule.map_sup,Submodule.map_span]

end FourPapers.Sublattice

end
end ExtensionSource2


/- SOURCE FourPapers.Sublattice.SquarefreeFaceContraction -/
section ExtensionSource3

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma forbiddenKoszulFaces_insert_of_two_le {B : Family V}
    {α : Exponent V} {e : V} (hB : ∀b∈B, b e≤1) (hα : 2≤α e)
    (F : Finset V) :
    forbiddenKoszulFaces B α (insert e F) ↔ forbiddenKoszulFaces B α F := by
  constructor
  · exact forbiddenKoszulFaces_downward B α (Finset.subset_insert e F)
  · rintro ⟨b,hb,hbα⟩
    refine ⟨b,hb,?_⟩
    intro v
    by_cases hv : v=e
    · subst v
      have hbe := hB b hb
      simp only [Finsupp.tsub_apply,faceExponent_apply,Finset.mem_insert_self,ite_true]
      omega
    · simpa [Finsupp.tsub_apply,faceExponent_apply,hv] using hbα v

/-- A quotient face remains allowed when a present variable is inserted. -/
lemma quotientKoszulFaces_insert_of_pos {B : Family V} {α : Exponent V}
    {e : V} (hα : 0<α e) {F : Finset V} (hF : quotientKoszulFaces B α F) :
    quotientKoszulFaces B α (insert e F) :=
  ⟨fullKoszulFaces_insert hα hF.1,
    fun h => hF.2 (forbiddenKoszulFaces_downward B α (Finset.subset_insert e F) h)⟩

/-- A repeated coordinate in a squarefree monomial ideal gives a literal
contraction of the actual quotient strand. -/
theorem quotientTotalCreation_contracts_of_two_le {B : Family V}
    {α : Exponent V} {e : V} (hB : ∀b∈B, b e≤1) (hα : 2≤α e) :
    quotientTotalDifferential (k := k) B α ∘ₗ quotientTotalCreation B α e +
      quotientTotalCreation B α e ∘ₗ quotientTotalDifferential B α = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change quotientFaceProjection B α (Simplicial.boundary
      (quotientFaceProjection B α (Simplicial.creation e x.val))) +
    quotientFaceProjection B α (Simplicial.creation e
      (quotientFaceProjection B α (Simplicial.boundary x.val))) = x.val
  unfold quotientFaceProjection
  refine relative_contraction_identity (K := k) (M := Simplicial.Ambient V k)
    (I := Finset V) (Simplicial.basis (k := k)) (fullKoszulFaces α)
    (forbiddenKoszulFaces B α) (Simplicial.boundary (k := k))
    (Simplicial.creation (k := k) e) ?_ ?_ ?_ ?_ ?_ x.property
  · exact fun _ hx => boundary_mem_basisSpan (fullKoszulFaces_downward α) hx
  · exact fun _ hx => creation_mem_basisSpan e
      (fun _ hs => fullKoszulFaces_insert (by omega) hs) hx
  · exact fun _ hx => boundary_mem_basisSpan (forbiddenKoszulFaces_downward B α) hx
  · exact fun _ hx => creation_mem_basisSpan e
      (fun F hF => (forbiddenKoszulFaces_insert_of_two_le hB hα F).mpr hF) hx
  · intro y
    rw [Simplicial.boundary_creation]
    exact sub_add_cancel _ _

/-- The previous explicit contraction annihilates all homology in repeated
fine degrees, over arbitrary coefficient rings. -/
theorem quotient_cycle_boundary_of_two_le {B : Family V}
    {α : Exponent V} {e : V} (hB : ∀b∈B, b e≤1) (hα : 2≤α e)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces B α))
    (hx : quotientTotalDifferential B α x=0) :
    x∈LinearMap.range (quotientTotalDifferential B α) := by
  refine ⟨quotientTotalCreation B α e x,?_⟩
  have h := LinearMap.congr_fun (quotientTotalCreation_contracts_of_two_le hB hα) x
  change quotientTotalDifferential B α (quotientTotalCreation B α e x) +
    quotientTotalCreation B α e (quotientTotalDifferential B α x)=x at h
  simpa only [hx,map_zero,add_zero] using h

end FourPapers.Sublattice

end
end ExtensionSource3


/- SOURCE FourPapers.Sublattice.GraphPreparationSource -/
section ExtensionSource4

end ExtensionSource4


end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientSeparatedFactors -/
section

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped TensorProduct
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- The family generating a coordinate-variable ideal. -/
def variableMonomialFamily (L : Finset V) : Family V :=
  L.image (fun v => Finsupp.single v 1)

lemma contains_variableMonomialFamily (L : Finset V) (α : Exponent V) :
    Contains (variableMonomialFamily L) α ↔ ∃v∈L, 0<α v := by
  constructor
  · rintro ⟨b,hb,hbα⟩
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hb
    refine ⟨v,hv,?_⟩
    simpa only [Finsupp.single_eq_same, Nat.succ_le_iff] using hbα v
  · rintro ⟨v,hv,hvα⟩
    exact ⟨_,Finset.mem_image.mpr ⟨v,hv,rfl⟩,Finsupp.single_le_iff.mpr hvα⟩

lemma quotientVariableFamily_face_eq {L : Finset V} {α : Exponent V}
    (hα : ∀v, α v≠0 → v∈L) {F : Finset V}
    (hF : quotientKoszulFaces (variableMonomialFamily L) α F) : α=faceExponent F := by
  apply le_antisymm
  · intro v
    by_cases hv : v∈L
    · have hzero : α v-(faceExponent F) v=0 := by
        by_contra hn
        apply hF.2
        apply (contains_variableMonomialFamily L _).mpr
        exact ⟨v,hv,by simpa only [Finsupp.tsub_apply] using Nat.pos_of_ne_zero hn⟩
      omega
    · have hz : α v=0 := by
        by_contra hn
        exact hv (hα v hn)
      simp [hz]
  · exact hF.1

lemma quotientVariableFamily_faces_iff {L : Finset V} {α : Exponent V}
    (hα : ∀v, α v≠0 → v∈L) (F : Finset V) :
    quotientKoszulFaces (variableMonomialFamily L) α F ↔ faceExponent F=α := by
  constructor
  · intro hF
    exact (quotientVariableFamily_face_eq hα hF).symm
  · intro hF
    refine ⟨hF.le,?_⟩
    change ¬Contains (variableMonomialFamily L) (α-faceExponent F)
    rw [hF,tsub_self,contains_variableMonomialFamily]
    simp

lemma quotientSeparated_faces
    (S : V → Prop) (B C : Family V)
    (hB : ∀b∈B, ∀v, b v≠0 → S v)
    (hC : ∀c∈C, ∀v, c v≠0 → ¬S v)
    (α : Exponent V) (F : Finset V) :
    quotientKoszulFaces (B∪C) α F ↔
      splitFacePredicate S (quotientKoszulFaces B (α.filter S))
        (quotientKoszulFaces C (α.filter (fun v => ¬S v))) F := by
  have hcontains : ∀v, Contains (B∪C) v ↔
      Contains B (v.filter S) ∨ Contains C (v.filter (fun x => ¬S x)) := by
    intro v
    rw [contains_filter_iff_of_supported B S hB,
      contains_filter_iff_of_supported C (fun x => ¬S x) hC]
    constructor
    · rintro ⟨b,hb,hbv⟩
      rcases Finset.mem_union.mp hb with hb | hb
      · exact Or.inl ⟨b,hb,hbv⟩
      · exact Or.inr ⟨b,hb,hbv⟩
    · rintro (⟨b,hb,hbv⟩ | ⟨b,hb,hbv⟩)
      · exact ⟨b,Finset.mem_union_left _ hb,hbv⟩
      · exact ⟨b,Finset.mem_union_right _ hb,hbv⟩
  have hfull : fullKoszulFaces α F ↔
      fullKoszulFaces (α.filter S) (F.filter S) ∧
      fullKoszulFaces (α.filter (fun v => ¬S v)) (F.filter (fun v => ¬S v)) := by
    constructor
    · intro hf
      constructor
      · intro v
        by_cases hv : S v <;>
          simp only [fullKoszulFaces,faceExponent_apply,Finset.mem_filter,
            Finsupp.filter_apply,hv,and_true,and_false,ite_false,ite_true] at *
        · simpa only [faceExponent_apply] using hf v
        · exact zero_le
      · intro v
        by_cases hv : S v <;>
          simp only [fullKoszulFaces,faceExponent_apply,Finset.mem_filter,
            Finsupp.filter_apply,hv,not_true_eq_false,not_false_eq_true,
            and_true,and_false,ite_false,ite_true] at *
        · exact zero_le
        · simpa only [faceExponent_apply] using hf v
    · rintro ⟨hl,hr⟩ v
      by_cases hv : S v
      · simpa [Finsupp.filter_apply,faceExponent_apply,hv] using hl v
      · simpa [Finsupp.filter_apply,faceExponent_apply,hv] using hr v
  simp only [quotientKoszulFaces,forbiddenKoszulFaces,splitFacePredicate,
    hcontains,filter_residual_face,hfull,not_or]
  tauto

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.VariableQuotientHomology -/
section

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma variableMonomialFamily_unused (L : Finset V) {e : V} (he : e∉L) :
    UnusedVariable (variableMonomialFamily L) e := by
  intro b hb
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hb
  have hvne : v≠e := fun h => he (h ▸ hv)
  simp [Finsupp.single_apply,hvne,Ne.symm hvne]

lemma degree_faceExponent (F : Finset V) : (faceExponent F).degree = F.card := by
  classical
  simp [faceExponent, map_sum, Finsupp.degree_single]

/-- Coordinate-variable quotient homology is concentrated in the unique
possible exterior degree. The proof works over every coefficient ring and
returns an actual homogeneous boundary, including outside the support of the
killed variables. -/
theorem variableQuotientCycle_boundary_of_degree_ne
    (B : Family V) (L : Finset V)
    (hB : ∀v,Contains (variableMonomialFamily L) v ↔ Contains B v)
    (α : Exponent V) (p : ℕ) (hp : p≠α.degree)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces B α))
    (hx : x∈totalFacePiece (quotientKoszulFaces B α) p)
    (hdx : quotientTotalDifferential B α x=0) :
    ∃y : TotalFaceModule (k := k) (quotientKoszulFaces B α),
      y∈totalFacePiece (quotientKoszulFaces B α) (p+1) ∧
      quotientTotalDifferential B α y=x := by
  by_cases hα : ∀v,α v≠0→v∈L
  · have hz : x.val=0 := by
      have hbot : Simplicial.Chains (k := k) (quotientKoszulFaces B α) p ≤ ⊥ := by
        apply Submodule.span_le.mpr
        rintro z ⟨F, ⟨hF, hcard⟩, rfl⟩
        have hF' : quotientKoszulFaces (variableMonomialFamily L) α F := by
          simpa only [quotientKoszulFaces_eq_of_contains hB α] using hF
        have he := congrArg Finsupp.degree (quotientVariableFamily_face_eq hα hF')
        rw [degree_faceExponent, hcard] at he
        exact False.elim (hp he.symm)
      simpa only [Submodule.mem_bot, Submodule.subtype_apply] using hbot hx
    have hzx : x=0 := Subtype.ext hz
    exact ⟨0,Submodule.zero_mem _,by rw [map_zero,hzx]⟩
  · push_neg at hα
    obtain ⟨e,heα,heL⟩ := hα
    have he := variableMonomialFamily_unused L heL
    have hpα : 0<α e := Nat.pos_of_ne_zero heα
    refine ⟨quotientTotalCreation B α e x,
      quotientTotalCreation_raises_of_contains hB he hpα p x hx,?_⟩
    have hc := LinearMap.congr_fun
      (quotientTotalCreation_contracts_of_contains (k := k) hB he hpα) x
    change quotientTotalDifferential B α (quotientTotalCreation B α e x)+
      quotientTotalCreation B α e (quotientTotalDifferential B α x)=x at hc
    simpa only [hdx,map_zero,add_zero] using hc

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.BlockCycleBoundary -/
section

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- Boundary filling in each literal coefficient quotient transfers through
the already proved all-powers chain isomorphism, preserving exterior degree. -/
theorem allPowerCycle_boundary_of_blocks (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0< m) (α : Exponent (FiniteVariable.{u} n)) (p : ℕ)
    (hfill : ∀w : AdmissibleChain n E m α,
      ∀x : TotalFaceModule (k := k)
        (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
          (α-finiteChainShift n w.val)),
        x∈totalFacePiece (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
          (α-finiteChainShift n w.val)) p →
        quotientTotalDifferential (finiteChainCoefficientFamily n w.val)
          (α-finiteChainShift n w.val) x=0 →
        ∃y, y∈totalFacePiece (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
          (α-finiteChainShift n w.val)) (p+1) ∧
          quotientTotalDifferential (finiteChainCoefficientFamily n w.val)
            (α-finiteChainShift n w.val) y=x)
    (x : TotalFaceModule (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α))
    (hx : x∈totalFacePiece (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α) p)
    (hdx : idealTotalDifferential
      (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) m) α) x=0) :
    ∃y : TotalFaceModule (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α),
      y∈totalFacePiece (koszulFaces (exponentPowerFamily (finiteRowFamily n E) m) α) (p+1) ∧
      idealTotalDifferential
        (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) m) α) y=x := by
  obtain ⟨e,he,hchain,hpres,hinv⟩ := allPowerGradedChainEquiv_exists (k := k) hE m hm α
  let t := chainTotalEquiv hE m α k
  let z := e.symm (t.symm x)
  have hzdeg : z∈chainTotalPiece n E m α k p :=
    hinv p (t.symm x) (chainTotalEquiv_symm_preserves_chainTotalPiece hE p x hx)
  have hzd : chainTotalSpecialDifferential n E m α k z=0 := by
    apply e.injective
    rw [map_zero]
    have hc := LinearMap.congr_fun hchain z
    change chainTotalOrdinaryDifferential hE m α k (e z)=
      e (chainTotalSpecialDifferential n E m α k z) at hc
    rw [←hc]
    simp only [z,LinearEquiv.apply_symm_apply,chainTotalOrdinaryDifferential,
      LinearMap.comp_apply,LinearEquiv.coe_coe,t,LinearEquiv.apply_symm_apply,hdx,map_zero]
  have hf : ∀w : AdmissibleChain n E m α,
      ∃y : TotalFaceModule (k := k)
        (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
          (α-finiteChainShift n w.val)),
        y∈totalFacePiece (quotientKoszulFaces (finiteChainCoefficientFamily n w.val)
          (α-finiteChainShift n w.val)) (p+1) ∧
        quotientTotalDifferential (finiteChainCoefficientFamily n w.val)
          (α-finiteChainShift n w.val) y=z w := by
    intro w
    apply hfill w (z w) ((chainTotalPiece_iff p z).mp hzdeg w)
    exact congrArg (fun y => y w) hzd
  let y : ChainTotalModule n E m α k :=
    DFinsupp.equivFunOnFintype.symm (fun w => (hf w).choose)
  have hydeg : y∈chainTotalPiece n E m α k (p+1) := by
    apply (chainTotalPiece_iff (p+1) y).mpr
    intro w
    exact (hf w).choose_spec.1
  have hyd : chainTotalSpecialDifferential n E m α k y=z := by
    apply DFinsupp.ext
    intro w
    change quotientTotalDifferential (finiteChainCoefficientFamily n w.val)
      (α-finiteChainShift n w.val) ((hf w).choose) = z w
    exact (hf w).choose_spec.2
  refine ⟨t (e y),chainTotalEquiv_preserves_chainTotalPiece hE (p+1) (e y)
    (hpres (p+1) y hydeg),?_⟩
  have hc := congrArg t (LinearMap.congr_fun hchain y)
  change t (t.symm (idealTotalDifferential
    (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) m) α)
      (t (e y))))=t (e (chainTotalSpecialDifferential n E m α k y)) at hc
  simpa only [t.apply_symm_apply,hyd,z,e.apply_symm_apply] using hc

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.LinearColonHomology -/
section

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- A sublattice whose genuine predecessor colons are generated by variables
has a linear resolution in the explicit homogeneous cycle-and-boundary sense.
This is derived from the complete chain comparison, over every ring. -/
theorem firstPowerCycle_boundary_of_linear_colons (hE : finiteLatticeClosed n E)
    (hlinear : ∀a : E, ∃L : Finset (FiniteVariable.{u} n),
      ∀v, Contains (variableMonomialFamily L) v ↔ Contains (finitePredecessorFamily n E a.val) v)
    (α : Exponent (FiniteVariable.{u} n)) (p : ℕ) (hp : α.degree≠p+d)
    (x : TotalFaceModule (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) α))
    (hx : x∈totalFacePiece (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) α) p)
    (hdx : idealTotalDifferential
      (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) 1) α) x=0) :
    ∃y : TotalFaceModule (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) α),
      y∈totalFacePiece (koszulFaces (exponentPowerFamily (finiteRowFamily n E) 1) α) (p+1) ∧
      idealTotalDifferential
        (koszulFaces_downward (exponentPowerFamily (finiteRowFamily n E) 1) α) y=x := by
  apply allPowerCycle_boundary_of_blocks hE 1 (by decide) α p _ x hx hdx
  intro w z hz hdz
  obtain ⟨L,hL⟩ := hlinear (w.val.val 0)
  have he : finiteChainCoefficientFamily n w.val=
      finitePredecessorFamily n E (w.val.val 0).val := by
    exact (congrArg (finiteChainCoefficientFamily n) (singletonChain_eq w.val).symm).trans
      (singletonChain_coefficient (w.val.val 0))
  have hdegree : (α-finiteChainShift n w.val).degree+d=α.degree := by
    have hh := congrArg Finsupp.degree (tsub_add_cancel_of_le w.property)
    simpa only [map_add,finiteChainShift_degree,one_mul] using hh
  apply variableQuotientCycle_boundary_of_degree_ne _ L
    (fun v => by rw [he]; exact hL v) _ p _ z hz hdz
  intro h
  exact hp (by omega)

variable {N : ℕ}

lemma graph_linear_colons_of_residual_empty {G : SimpleGraph (Fin N)}
    (hG : IntervalLabeling G)
    (hempty : ∀a∈graphEdgeLattice G,graphResidualEdges G a=∅) :
    ∀a : graphEdgeLattice G, ∃L : Finset (FiniteVariable.{u} (GraphRows N)),
      ∀v, Contains (variableMonomialFamily L) v ↔
        Contains (finitePredecessorFamily (GraphRows N) (graphEdgeLattice G) a.val) v := by
  intro a
  refine ⟨graphLinearVariables G a.val,?_⟩
  intro v
  rw [← finiteCoordinatePredecessor_contains_iff (graphEdgeLattice_closed hG) a.property,
    graphCoordinateColon_contains_iff hG a.property]
  simp [Contains, graphColonFamily, variableMonomialFamily,
    hempty a.val a.property, finiteRowFamily]

/-- A complete interval, with all other vertices isolated. The use of the
original vertex set keeps every later quotient map literal. -/
def intervalCliqueGraph (l r : Fin N) : SimpleGraph (Fin N) where
  Adj x y := x≠y ∧ l≤x ∧ x≤r ∧ l≤y ∧ y≤r
  symm := ⟨fun x y h => ⟨h.1.symm,h.2.2.2.1,h.2.2.2.2,h.2.1,h.2.2.1⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

lemma intervalCliqueGraph_interval (l r : Fin N) : IntervalLabeling (intervalCliqueGraph l r) := by
  intro x y z hxy hyz hxz
  exact ⟨⟨hxy.ne,hxz.2.1,hxz.2.2.1,hxz.2.1.trans hxy.le,
      hyz.le.trans hxz.2.2.2.2⟩,
    ⟨hyz.ne,hxz.2.1.trans hxy.le,hyz.le.trans hxz.2.2.2.2,
      hxz.2.2.2.1,hxz.2.2.2.2⟩⟩

lemma intervalCliqueGraph_residual_empty (l r : Fin N)
    {a : FiniteTuple (GraphRows N)} (ha : a∈graphEdgeLattice (intervalCliqueGraph l r)) :
    graphResidualEdges (intervalCliqueGraph l r) a=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro b hb
  rcases (graphResidualEdges_variable_restriction _ a b).mp hb with ⟨hb,hnot,hba⟩
  have ha' := (mem_graphEdgeLattice _ a).mp ha
  have hb' := (mem_graphEdgeLattice _ b).mp hb
  apply hnot
  exact ⟨((hb'.1.trans_le hba).trans ha'.1).ne,
    hb'.2.2.1,hb'.2.2.2.1,ha'.2.2.2.2.1,ha'.2.2.2.2.2⟩

/-- Actual homogeneous ideal cycles for a clique have precisely the linear
resolution degree. This theorem includes arbitrary characteristic and torsion
in the coefficient ring, and returns a genuine degree-preserving filling. -/
theorem intervalClique_idealCycle_boundary (l r : Fin N)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) (p : ℕ) (hp : α.degree≠p+2)
    (x : TotalFaceModule (k := k)
      (koszulFaces (exponentPowerFamily (finiteRowFamily (GraphRows N)
        (graphEdgeLattice (intervalCliqueGraph l r))) 1) α))
    (hx : x∈totalFacePiece (koszulFaces (exponentPowerFamily
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) 1) α) p)
    (hdx : idealTotalDifferential (koszulFaces_downward (exponentPowerFamily
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) 1) α) x=0) :
    ∃y, y∈totalFacePiece (koszulFaces (exponentPowerFamily
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) 1) α) (p+1) ∧
      idealTotalDifferential (koszulFaces_downward (exponentPowerFamily
        (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) 1) α) y=x :=
  firstPowerCycle_boundary_of_linear_colons
    (graphEdgeLattice_closed (intervalCliqueGraph_interval l r))
    (graph_linear_colons_of_residual_empty (intervalCliqueGraph_interval l r)
      (fun a ha => intervalCliqueGraph_residual_empty l r ha)) α p hp x hx hdx

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientFaceProduct -/
section

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

/-!
# Multiplication in the actual monomial quotient Koszul strands

The product is projected after exterior multiplication. In particular, the
surviving-face subspace is not assumed to be closed under the ambient product.
The discarded terms form the actual monomial-ideal subcomplex, which proves
compatibility with projection and the Leibniz identity.
-/

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma relativeProjection_sub_mem_full_discarded
    {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis I R M) (P Q : I → Prop) {x : M}
    (hx : x∈basisSpan b P) :
    relativeProjection b P Q x-x∈basisSpan b (fun i => P i ∧ Q i) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,hi,rfl⟩ := hx
    change P i at hi
    by_cases hq : Q i
    · simpa [hi,hq] using
        (basisSpan b (fun i => P i ∧ Q i)).neg_mem
          (Submodule.subset_span ⟨i,⟨hi,hq⟩,rfl⟩)
    · simp [hi,hq]
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa [add_sub_add_comm] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    simpa [smul_sub] using Submodule.smul_mem _ c ih

lemma fullKoszulFaces_union (α β : Exponent V) (F G : Finset V)
    (hF : fullKoszulFaces α F) (hG : fullKoszulFaces β G)
    (hFG : Disjoint F G) : fullKoszulFaces (α+β) (F∪G) := by
  change faceExponent (F∪G)≤α+β
  rw [faceExponent_union_of_disjoint F G hFG]
  exact add_le_add hF hG

lemma fullFaceSpan_mul (α β : Exponent V) {x y : Simplicial.Ambient V k}
    (hx : x∈TotalFaceModule (fullKoszulFaces α))
    (hy : y∈TotalFaceModule (fullKoszulFaces β)) :
    x*y∈TotalFaceModule (fullKoszulFaces (α+β)) :=
  faceSpan_mul_mem _ _ _ (fun F hF G hG hFG =>
    fullKoszulFaces_union α β F G hF hG hFG) hx hy

lemma quotientFaceProjection_full (B : Family V) (α : Exponent V)
    (x : Simplicial.Ambient V k) :
    quotientFaceProjection B α x∈TotalFaceModule (fullKoszulFaces α) :=
  Submodule.span_mono (Set.image_mono (fun _ hs => hs.1))
    (relativeProjection_mem _ _ _ x)

lemma discardedFace_mul_full (B : Family V) (α β : Exponent V)
    {x y : Simplicial.Ambient V k}
    (hx : x∈basisSpan Simplicial.basis
      (fun F => fullKoszulFaces α F ∧ forbiddenKoszulFaces B α F))
    (hy : y∈TotalFaceModule (fullKoszulFaces β)) :
    x*y∈basisSpan Simplicial.basis (forbiddenKoszulFaces B (α+β)) := by
  apply faceSpan_mul_mem _ _ _ _ hx hy
  intro F hF G hG hFG
  rcases hF.2 with ⟨b,hb,hbF⟩
  refine ⟨b,hb,?_⟩
  rw [residual_union_of_disjoint α β F G hFG hF.1 hG]
  exact hbF.trans le_self_add

lemma fullFace_mul_discarded (B : Family V) (α β : Exponent V)
    {x y : Simplicial.Ambient V k}
    (hx : x∈TotalFaceModule (fullKoszulFaces α))
    (hy : y∈basisSpan Simplicial.basis
      (fun G => fullKoszulFaces β G ∧ forbiddenKoszulFaces B β G)) :
    x*y∈basisSpan Simplicial.basis (forbiddenKoszulFaces B (α+β)) := by
  apply faceSpan_mul_mem _ _ _ _ hx hy
  intro F hF G hG hFG
  rcases hG.2 with ⟨b,hb,hbG⟩
  refine ⟨b,hb,?_⟩
  rw [residual_union_of_disjoint α β F G hFG hF hG.1]
  exact hbG.trans le_add_self

lemma quotientFaceProjection_mul_left (B : Family V) (α β : Exponent V)
    {x y : Simplicial.Ambient V k}
    (hx : x∈TotalFaceModule (fullKoszulFaces α))
    (hy : y∈TotalFaceModule (fullKoszulFaces β)) :
    quotientFaceProjection B (α+β) (quotientFaceProjection B α x*y)=
      quotientFaceProjection B (α+β) (x*y) := by
  have hz := relativeProjection_zero_on_discarded (Simplicial.basis (k := k))
    (fullKoszulFaces (α+β)) (forbiddenKoszulFaces B (α+β))
    (discardedFace_mul_full B α β
      (relativeProjection_sub_mem_full_discarded (Simplicial.basis (k := k))
        (fullKoszulFaces α) (forbiddenKoszulFaces B α) hx) hy)
  change quotientFaceProjection B (α+β) ((quotientFaceProjection B α x-x)*y)=0 at hz
  rw [sub_mul,map_sub] at hz
  exact sub_eq_zero.mp hz

lemma quotientFaceProjection_mul_right (B : Family V) (α β : Exponent V)
    {x y : Simplicial.Ambient V k}
    (hx : x∈TotalFaceModule (fullKoszulFaces α))
    (hy : y∈TotalFaceModule (fullKoszulFaces β)) :
    quotientFaceProjection B (α+β) (x*quotientFaceProjection B β y)=
      quotientFaceProjection B (α+β) (x*y) := by
  have hz := relativeProjection_zero_on_discarded (Simplicial.basis (k := k))
    (fullKoszulFaces (α+β)) (forbiddenKoszulFaces B (α+β))
    (fullFace_mul_discarded B α β hx
      (relativeProjection_sub_mem_full_discarded (Simplicial.basis (k := k))
        (fullKoszulFaces β) (forbiddenKoszulFaces B β) hy))
  change quotientFaceProjection B (α+β) (x*(quotientFaceProjection B β y-y))=0 at hz
  rw [mul_sub,map_sub] at hz
  exact sub_eq_zero.mp hz

/-- Projection is compatible with the literal quotient multiplication. -/
lemma quotientFaceProjection_mul (B : Family V) (α β : Exponent V)
    {x y : Simplicial.Ambient V k}
    (hx : x∈TotalFaceModule (fullKoszulFaces α))
    (hy : y∈TotalFaceModule (fullKoszulFaces β)) :
    quotientFaceProjection B (α+β)
        (quotientFaceProjection B α x*quotientFaceProjection B β y)=
      quotientFaceProjection B (α+β) (x*y) := by
  rw [quotientFaceProjection_mul_left B α β hx (quotientFaceProjection_full B β y),
    quotientFaceProjection_mul_right B α β hx hy]

lemma quotientFaceProjection_boundary (B : Family V) (α : Exponent V)
    {x : Simplicial.Ambient V k} (hx : x∈TotalFaceModule (fullKoszulFaces α)) :
    quotientFaceProjection B α (Simplicial.boundary (quotientFaceProjection B α x))=
      quotientFaceProjection B α (Simplicial.boundary x) :=
  relativeProjection_map_projection (Simplicial.basis (k := k)) (fullKoszulFaces α)
    (forbiddenKoszulFaces B α) (Simplicial.boundary (k := k))
    (fun _ hz => boundary_mem_basisSpan (forbiddenKoszulFaces_downward B α) hz) hx

/-- Projected exterior multiplication satisfies the actual differential's
Leibniz rule, with the characteristic-free grade involution. -/
theorem quotientFaceProjection_product_differential
    (B : Family V) (α β : Exponent V) {x y : Simplicial.Ambient V k}
    (hx : x∈TotalFaceModule (fullKoszulFaces α))
    (hy : y∈TotalFaceModule (fullKoszulFaces β)) :
    quotientFaceProjection B (α+β) (Simplicial.boundary
      (quotientFaceProjection B (α+β) (x*y))) =
      quotientFaceProjection B (α+β)
        (quotientFaceProjection B α (Simplicial.boundary x)*y) +
      quotientFaceProjection B (α+β)
        (CliffordAlgebra.involute x*quotientFaceProjection B β (Simplicial.boundary y)) := by
  rw [quotientFaceProjection_boundary B (α+β) (fullFaceSpan_mul α β hx hy)]
  rw [show Simplicial.boundary (x*y)=Simplicial.boundary x*y+
      CliffordAlgebra.involute x*Simplicial.boundary y from
    CliffordAlgebra.contractLeft_mul _ x y,map_add]
  rw [quotientFaceProjection_mul_left B α β
      (boundary_mem_basisSpan (fullKoszulFaces_downward α) hx) hy,
    quotientFaceProjection_mul_right B α β
      (faceSpan_involute_mem (fullKoszulFaces α) hx)
      (boundary_mem_basisSpan (fullKoszulFaces_downward β) hy)]

/-- Products of genuine quotient cycles are again genuine quotient cycles. -/
theorem quotientFaceProjection_product_cycle
    (B : Family V) (α β : Exponent V) {x y : Simplicial.Ambient V k}
    (hx : x∈TotalFaceModule (fullKoszulFaces α))
    (hy : y∈TotalFaceModule (fullKoszulFaces β))
    (hdx : quotientFaceProjection B α (Simplicial.boundary x)=0)
    (hdy : quotientFaceProjection B β (Simplicial.boundary y)=0) :
    quotientFaceProjection B (α+β) (Simplicial.boundary
      (quotientFaceProjection B (α+β) (x*y)))=0 := by
  rw [quotientFaceProjection_product_differential B α β hx hy,hdx,hdy,
    zero_mul,mul_zero,map_zero,add_zero]

/-- The actual quotient multiplication, in fixed fine degrees. -/
def quotientFaceMul (B : Family V) (α β : Exponent V)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces B α))
    (y : TotalFaceModule (k := k) (quotientKoszulFaces B β)) :
    TotalFaceModule (k := k) (quotientKoszulFaces B (α+β)) :=
  ⟨quotientFaceProjection B (α+β) (x.val*y.val),relativeProjection_mem _ _ _ _⟩

lemma quotientFaceMul_cycle (B : Family V) (α β : Exponent V)
    (x : TotalFaceModule (k := k) (quotientKoszulFaces B α))
    (y : TotalFaceModule (k := k) (quotientKoszulFaces B β))
    (hx : quotientTotalDifferential B α x=0)
    (hy : quotientTotalDifferential B β y=0) :
    quotientTotalDifferential B (α+β) (quotientFaceMul B α β x y)=0 := by
  apply Subtype.ext
  exact quotientFaceProjection_product_cycle B α β
    (Submodule.span_mono (Set.image_mono (fun _ h => h.1)) x.property)
    (Submodule.span_mono (Set.image_mono (fun _ h => h.1)) y.property)
    (congrArg Subtype.val hx) (congrArg Subtype.val hy)

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IdealQuotientFilling -/
section

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma quotientFaceProjection_sub_mem_ideal_degree (B : Family V) (α : Exponent V) (i : ℕ)
    {x : Simplicial.Ambient V k} (hx : x∈Simplicial.Chains (fullKoszulFaces α) i) :
    quotientFaceProjection B α x-x∈Simplicial.Chains (koszulFaces B α) i := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F,⟨hF,hcard⟩,rfl⟩ := hx
    by_cases hb : forbiddenKoszulFaces B α F
    · simpa [quotientFaceProjection,hF,hb] using
        (Simplicial.Chains (k := k) (koszulFaces B α) i).neg_mem
          (Simplicial.basis_mem ⟨hF,hb⟩ hcard)
    · simp [quotientFaceProjection,hF,hb]
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa [add_sub_add_comm] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    simpa [smul_sub] using Submodule.smul_mem _ c ih

lemma quotientFaceProjection_zero_mem_ideal_degree (B : Family V) (α : Exponent V) (i : ℕ)
    {x : Simplicial.Ambient V k} (hx : x∈Simplicial.Chains (fullKoszulFaces α) i)
    (hq : quotientFaceProjection B α x=0) :
    x∈Simplicial.Chains (koszulFaces B α) i := by
  have hh := (Simplicial.Chains (k := k) (koszulFaces B α) i).neg_mem
    (quotientFaceProjection_sub_mem_ideal_degree B α i hx)
  simpa only [hq,zero_sub,neg_neg] using hh

lemma quotientFaceProjection_zero_on_ideal (B : Family V) (α : Exponent V)
    {x : Simplicial.Ambient V k} (hx : x∈TotalFaceModule (koszulFaces B α)) :
    quotientFaceProjection B α x=0 :=
  relativeProjection_zero_on_discarded (Simplicial.basis (k := k)) (fullKoszulFaces α)
    (forbiddenKoszulFaces B α)
    (Submodule.span_mono (Set.image_mono (fun _ hs => hs.2)) hx)

lemma quotientCycle_boundary_degree_zero (B : Family V) (α : Exponent V)
    (e : V) (he : 0<α e)
    (z : TotalFaceModule (k := k) (quotientKoszulFaces B α))
    (hz : z∈totalFacePiece (quotientKoszulFaces B α) 0) :
    ∃y, y∈totalFacePiece (quotientKoszulFaces B α) 1 ∧
      quotientTotalDifferential B α y=z := by
  have hzfull : z.val∈Simplicial.Chains (fullKoszulFaces α) 0 :=
    Simplicial.chains_mono (fun _ hs => hs.1) 0 hz
  have hcreation := creation_mem_chains e (fun _ hs => fullKoszulFaces_insert he hs) hzfull
  let y : TotalFaceModule (k := k) (quotientKoszulFaces B α) :=
    ⟨quotientFaceProjection B α (Simplicial.creation e z.val),relativeProjection_mem _ _ _ _⟩
  refine ⟨y,quotientFaceProjection_degree B α 1 hcreation,?_⟩
  apply Subtype.ext
  change quotientFaceProjection B α (Simplicial.boundary
    (quotientFaceProjection B α (Simplicial.creation e z.val)))=z.val
  rw [quotientFaceProjection_boundary B α (chains_mem_basisSpan hcreation),
    Simplicial.boundary_creation,Simplicial.boundary_zero_degree_zero hzfull,
    map_zero,sub_zero]
  exact relativeProjection_eq_self z.property

/-- The explicit contraction of the full polynomial strand converts a
homogeneous filling in the ideal strand into a homogeneous filling in its
actual quotient. No long exact sequence or assumed comparison map is used. -/
theorem quotientCycle_boundary_of_ideal_filling (B : Family V) (α : Exponent V)
    (e : V) (he : 0<α e) (p : ℕ)
    (hfill : ∀x : TotalFaceModule (k := k) (koszulFaces B α),
      x∈totalFacePiece (koszulFaces B α) p →
      idealTotalDifferential (koszulFaces_downward B α) x=0 →
      ∃y, y∈totalFacePiece (koszulFaces B α) (p+1) ∧
        idealTotalDifferential (koszulFaces_downward B α) y=x)
    (z : TotalFaceModule (k := k) (quotientKoszulFaces B α))
    (hz : z∈totalFacePiece (quotientKoszulFaces B α) (p+1))
    (hdz : quotientTotalDifferential B α z=0) :
    ∃y, y∈totalFacePiece (quotientKoszulFaces B α) (p+2) ∧
      quotientTotalDifferential B α y=z := by
  have hzfull : z.val∈Simplicial.Chains (fullKoszulFaces α) (p+1) :=
    Simplicial.chains_mono (fun _ hs => hs.1) (p+1) hz
  have hddeg := Simplicial.boundary_mem (fullKoszulFaces_downward α) hzfull
  have hdideal := quotientFaceProjection_zero_mem_ideal_degree B α p hddeg
    (congrArg Subtype.val hdz)
  let x : TotalFaceModule (k := k) (koszulFaces B α) :=
    ⟨Simplicial.boundary z.val,chains_mem_basisSpan hdideal⟩
  have hdx : idealTotalDifferential (koszulFaces_downward B α) x=0 := by
    apply Subtype.ext
    exact Simplicial.boundary_boundary z.val
  obtain ⟨a,hadeg,ha⟩ := hfill x hdideal hdx
  have haco : Simplicial.boundary a.val=Simplicial.boundary z.val := congrArg Subtype.val ha
  have hafull : a.val∈Simplicial.Chains (fullKoszulFaces α) (p+1) :=
    Simplicial.chains_mono (fun _ hs => hs.1) (p+1) hadeg
  have hdiff : z.val-a.val∈Simplicial.Chains (fullKoszulFaces α) (p+1) :=
    Submodule.sub_mem _ hzfull hafull
  have hclosed : Simplicial.boundary (z.val-a.val)=0 := by
    rw [map_sub,haco,sub_self]
  have hcreation := creation_mem_chains e (fun _ hs => fullKoszulFaces_insert he hs) hdiff
  let y : TotalFaceModule (k := k) (quotientKoszulFaces B α) :=
    ⟨quotientFaceProjection B α (Simplicial.creation e (z.val-a.val)),
      relativeProjection_mem _ _ _ _⟩
  refine ⟨y,quotientFaceProjection_degree B α (p+2) hcreation,?_⟩
  apply Subtype.ext
  change quotientFaceProjection B α (Simplicial.boundary
    (quotientFaceProjection B α (Simplicial.creation e (z.val-a.val))))=z.val
  rw [quotientFaceProjection_boundary B α (chains_mem_basisSpan hcreation),
    Simplicial.boundary_creation,hclosed,map_zero,sub_zero,map_sub,
    quotientFaceProjection_zero_on_ideal B α a.property,sub_zero]
  exact relativeProjection_eq_self z.property

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.CliqueQuotientHomology -/
section

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {k : Type u} [CommRing k] {N : ℕ}

lemma exponentPowerFamily_one {V : Type*} [DecidableEq V] (B : Family V) :
    exponentPowerFamily B 1=B := by
  ext a
  simp [exponentPowerFamily]

/-- The same identity with its decision procedure explicit, so rewriting
also applies to coordinate families using a different finite-variable
decision procedure from the one currently selected by typeclass search. -/
lemma exponentPowerFamily_one_of_decidable {V : Type*} (d : DecidableEq V)
    (B : Family V) : @exponentPowerFamily V d B 1 = B :=
  @exponentPowerFamily_one V d B

/-- Complete-interval quotient homology vanishes outside the linear strand in
every positive internal degree. This is an actual integral filling statement. -/
theorem intervalClique_quotientCycle_boundary (l r : Fin N)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) (p : ℕ)
    (hpos : 0<α.degree) (hp : α.degree≠p+1)
    (z : TotalFaceModule (k := k) (quotientKoszulFaces
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) α))
    (hz : z∈totalFacePiece (quotientKoszulFaces
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) α) p)
    (hdz : quotientTotalDifferential
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) α z=0) :
    ∃y, y∈totalFacePiece (quotientKoszulFaces
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) α) (p+1) ∧
      quotientTotalDifferential
        (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) α y=z := by
  obtain ⟨e,he⟩ : ∃e,0<α e := by
    by_contra hn
    push_neg at hn
    have ha : α=0 := by
      ext e
      exact Nat.eq_zero_of_le_zero (hn e)
    simp [ha] at hpos
  cases p with
  | zero => exact quotientCycle_boundary_degree_zero _ α e he z hz
  | succ p =>
    apply quotientCycle_boundary_of_ideal_filling _ α e he p _ z hz hdz
    intro x hx hdx
    have hp' : α.degree≠p+2 := by simpa only [Nat.succ_eq_add_one,Nat.add_assoc] using hp
    have hh := intervalClique_idealCycle_boundary (k := k) l r α p hp'
    rw [exponentPowerFamily_one_of_decidable] at hh
    exact hh x hx hdx

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.QuotientCoordinateConcentration -/
section

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 250000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma quotientPreviousDifferential_homogeneous (B : Family V) (p : ℕ)
    (t : QuotientIndex B p) :
    quotientPreviousDifferential B p (quotientCoefficientBasis (k := k) B p t)∈
      Grading.Piece (quotientCoefficientBasis B p.pred) quotientDegree (quotientDegree t) := by
  cases p with
  | zero => exact Submodule.zero_mem _
  | succ p => exact quotientDifferential_homogeneous B _ p (Grading.basis_mem_piece _ _ t)

lemma quotientFaceHomogeneousEquiv_differential (B : Family V) (α : Exponent V) (p : ℕ)
    (z : Simplicial.Chains (k := k) (quotientKoszulFaces B α) (p+1)) :
    quotientHomogeneousDifferential B α p (quotientFaceHomogeneousEquiv B α (p+1) z)=
      quotientFaceHomogeneousEquiv B α p (quotientFaceDifferential B α p z) := by
  simp only [quotientFaceDifferential,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

theorem quotientCoordinate_filling_of_face_filling
    (B : Family V) (α : Exponent V) (p : ℕ)
    (hfill : ∀z : TotalFaceModule (k := k) (quotientKoszulFaces B α),
      z∈totalFacePiece (quotientKoszulFaces B α) p → quotientTotalDifferential B α z=0 →
      ∃y,y∈totalFacePiece (quotientKoszulFaces B α) (p+1) ∧ quotientTotalDifferential B α y=z)
    (z : Set.powersetCard V p →₀ CoefficientQuotient (k := k) B)
    (hz : z∈quotientPiece (k := k) B α p) (hdz : quotientPreviousDifferential B p z=0) :
    ∃y,y∈quotientPiece (k := k) B α (p+1) ∧ quotientDifferential B p y=z := by
  let zf := (quotientFaceHomogeneousEquiv (k := k) B α p).symm ⟨z,hz⟩
  let zt : TotalFaceModule (k := k) (quotientKoszulFaces B α) :=
    ⟨zf.val,chains_mem_basisSpan zf.property⟩
  have hzt : zt∈totalFacePiece (quotientKoszulFaces B α) p := zf.property
  have hclosed : quotientTotalDifferential B α zt=0 := by
    cases p with
    | zero => exact quotientTotalDifferential_zero_degree B α zt hzt
    | succ p =>
      have hh : quotientFaceDifferential B α p zf=0 := by
        apply (quotientFaceHomogeneousEquiv B α p).injective
        rw [←quotientFaceHomogeneousEquiv_differential,LinearEquiv.apply_symm_apply,map_zero]
        apply Subtype.ext
        exact hdz
      have hv := congrArg Subtype.val hh
      rw [quotientFaceDifferential_val] at hv
      exact Subtype.ext hv
  obtain ⟨y,hy,hdy⟩ := hfill zt hzt hclosed
  let yf : Simplicial.Chains (k := k) (quotientKoszulFaces B α) (p+1) := ⟨y.val,hy⟩
  refine ⟨(quotientFaceHomogeneousEquiv B α (p+1) yf).val,
    (quotientFaceHomogeneousEquiv B α (p+1) yf).property,?_⟩
  have heq : quotientFaceDifferential B α p yf=zf := by
    apply Subtype.ext
    rw [quotientFaceDifferential_val]
    exact congrArg Subtype.val hdy
  have hh := quotientFaceHomogeneousEquiv_differential B α p yf
  rw [heq] at hh
  have hv := congrArg Subtype.val hh
  simp only [zf, LinearEquiv.apply_symm_apply] at hv
  change quotientDifferential (k := k) B p
    (quotientFaceHomogeneousEquiv (k := k) B α (p+1) yf).val = z at hv
  exact hv

theorem intervalClique_quotientCoordinateCycle_boundary {N : ℕ} (l r : Fin N)
    (α : Exponent (FiniteVariable.{u} (GraphRows N))) (p : ℕ)
    (hpos : 0<α.degree) (hp : α.degree≠p+1)
    (z : Set.powersetCard (FiniteVariable.{u} (GraphRows N)) p →₀
      CoefficientQuotient (k := k)
        (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))))
    (hz : z∈quotientPiece (k := k)
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) α p)
    (hdz : quotientPreviousDifferential
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) p z=0) :
    ∃y,y∈quotientPiece (k := k)
      (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) α (p+1) ∧
      quotientDifferential
        (finiteRowFamily (GraphRows N) (graphEdgeLattice (intervalCliqueGraph l r))) p y=z :=
  quotientCoordinate_filling_of_face_filling _ α p
    (intervalClique_quotientCycle_boundary l r α p hpos hp) z hz hdz

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Common.FilteredHomologyLifting -/
section

section
set_option maxRecDepth 4000
set_option maxHeartbeats 300000
set_option Elab.async false
/-! # Lifting cycles from vanishing graded homology

A literal cycle in a filtration level is filled by successively removing
its leading term.  Thus vanishing homology in the next chain degree gives
actual cycle lifts in the preceding degree.  No spectral-sequence assertion
is assumed, and no completeness or infinite summation is used.
-/
noncomputable section
set_option autoImplicit false
namespace FourPapers.FilteredHomology
open Classical
variable {K : Type*} [CommRing K]
variable {X Y Z : Type*} [AddCommGroup X] [Module K X]
  [AddCommGroup Y] [Module K Y] [AddCommGroup Z] [Module K Z]
variable (F : Filtration (K := K) X) (G : Filtration (K := K) Y)
  (H : Filtration (K := K) Z) (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z)
  (hf : Preserves F G f) (hg : Preserves G H g) (hfg : g.comp f = 0)

/-- The exact representative formulation of vanishing graded homology. -/
theorem leading_boundary_of_gradedHomology_subsingleton (n : ℕ)
    (hvanish : Subsingleton (GradedHomology F G H f g hf hg hfg n))
    (y : Y) (hy : y ∈ G.level (n + 1)) (hgy : g y = 0) :
    ∃ x, x ∈ F.level (n + 1) ∧ y - f x ∈ G.level n := by
  letI := hvanish
  exact (leadingHomologyClass_eq_zero_iff F G H f g hf hg hfg n
    ⟨⟨y, hgy⟩, hy⟩).mp (Subsingleton.elim _ _)

/-- Finite downward correction fills every cycle in the same filtration
level when all associated graded homology modules vanish. -/
theorem filtered_boundary_of_gradedHomology_subsingleton
    (hvanish : ∀ n, Subsingleton (GradedHomology F G H f g hf hg hfg n))
    (n : ℕ) (y : Y) (hy : y ∈ G.level n) (hgy : g y = 0) :
    ∃ x, x ∈ F.level n ∧ f x = y := by
  induction n generalizing y with
  | zero =>
      have hy0 : y = 0 := by simpa only [G.zero, Submodule.mem_bot] using hy
      exact ⟨0, (F.level 0).zero_mem, by simpa only [map_zero] using hy0.symm⟩
  | succ n ih =>
      obtain ⟨a, ha, hya⟩ := leading_boundary_of_gradedHomology_subsingleton
        F G H f g hf hg hfg n (hvanish n) y hy hgy
      have hgya : g (y - f a) = 0 := by
        rw [map_sub, hgy, show g (f a) = 0 from LinearMap.congr_fun hfg a, sub_self]
      obtain ⟨b, hb, hfb⟩ := ih (y - f a) hya hgya
      refine ⟨a + b, (F.level (n + 1)).add_mem ha (F.mono (Nat.le_succ n) hb), ?_⟩
      rw [map_add, hfb]
      abel

/-- Vanishing in the following chain degree implies that every leading
cycle of `f` has an actual cycle lift with the same leading term. -/
theorem liftsCycles_of_gradedHomology_subsingleton
    (hvanish : ∀ n, Subsingleton (GradedHomology F G H f g hf hg hfg n)) :
    LiftsCycles F G f := by
  intro n x hx hfx
  obtain ⟨a, ha, hfa⟩ := filtered_boundary_of_gradedHomology_subsingleton
    F G H f g hf hg hfg hvanish n (f x) hfx (LinearMap.congr_fun hfg x)
  refine ⟨x - a, (F.level (n + 1)).sub_mem hx (F.mono (Nat.le_succ n) ha), ?_, ?_⟩
  · rw [map_sub, hfa, sub_self]
  · simpa only [sub_sub_cancel] using ha

/-- A filtered differential becomes strict under the same vanishing
hypothesis.  The representative has precisely the requested filtration
bound, even if the original preimage has higher degree. -/
theorem strict_of_gradedHomology_subsingleton
    (hvanish : ∀ n, Subsingleton (GradedHomology F G H f g hf hg hfg n))
    (n : ℕ) (x : X) (hx : f x ∈ G.level n) :
    ∃ y, y ∈ F.level n ∧ f y = f x :=
  strict_of_liftsCycles F G f
    (liftsCycles_of_gradedHomology_subsingleton F G H f g hf hg hfg hvanish) n x hx


/-- A genuine homogeneous splitting supplies cycle lifts without solving any
linear equations.  The top projection commutes with the actual differential. -/
theorem liftsCycles_of_projections
    (p : ℕ → Module.End K X) (q : ℕ → Module.End K Y)
    (hp : ∀ n x, x ∈ F.level (n + 1) → p n x ∈ F.level (n + 1))
    (hlower : ∀ n x, x ∈ F.level (n + 1) → x - p n x ∈ F.level n)
    (hq : ∀ n y, y ∈ G.level n → q n y = 0)
    (hcomm : ∀ n, f.comp (p n) = (q n).comp f) : LiftsCycles F G f := by
  intro n x hx hfx
  refine ⟨p n x, hp n x hx, ?_, hlower n x hx⟩
  exact (LinearMap.congr_fun (hcomm n) x).trans (hq n (f x) hfx)

section Transport
variable {X' Y' : Type*} [AddCommGroup X'] [Module K X']
  [AddCommGroup Y'] [Module K Y']

/-- Transfer actual cycle lifts along an independently supplied filtered
chain isomorphism.  Both filtration directions are used explicitly. -/
theorem liftsCycles_of_filteredEquiv
    (F' : Filtration (K := K) X') (G' : Filtration (K := K) Y')
    (f' : X' →ₗ[K] Y') (eX : X ≃ₗ[K] X') (eY : Y ≃ₗ[K] Y')
    (hX : ∀ n x, eX x ∈ F'.level n ↔ x ∈ F.level n)
    (hY : ∀ n y, eY y ∈ G'.level n ↔ y ∈ G.level n)
    (hcomm : ∀ x, f' (eX x) = eY (f x))
    (hlift : LiftsCycles F G f) : LiftsCycles F' G' f' := by
  intro n x hx hfx
  have hy : f (eX.symm x) ∈ G.level n := by
    apply (hY n _).mp
    rw [← hcomm, LinearEquiv.apply_symm_apply]
    exact hfx
  obtain ⟨z, hz, hfz, hxz⟩ := hlift n (eX.symm x)
    ((hX (n + 1) _).mp (by simpa only [LinearEquiv.apply_symm_apply] using hx)) hy
  refine ⟨eX z, (hX (n + 1) z).mpr hz, ?_, ?_⟩
  · rw [hcomm, hfz, map_zero]
  · have h := (hX n _).mpr hxz
    simpa only [map_sub, LinearEquiv.apply_symm_apply] using h
end Transport

end FourPapers.FilteredHomology

#print axioms FourPapers.FilteredHomology.filtered_boundary_of_gradedHomology_subsingleton
#print axioms FourPapers.FilteredHomology.liftsCycles_of_gradedHomology_subsingleton
#print axioms FourPapers.FilteredHomology.strict_of_gradedHomology_subsingleton

/- BEGIN DEFINING-MODULE AUDIT -/



end
end
end


end
