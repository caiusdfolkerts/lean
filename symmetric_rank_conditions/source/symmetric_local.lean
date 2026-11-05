module
public import Lean
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Combinatorics.Young.YoungDiagram
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finsupp.Lex
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Sort
public import Mathlib.Data.List.GetD
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Order.WellFoundedSet
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Groebner
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Nullstellensatz
-- Tactic implementations used below are supplied by the specific imports.
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section


section
/- Source body: remote_vendor_MonomialOrder.lean -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Leading monomials for a monomial order

This file collects facts about leading monomials of multivariate polynomials for a monomial order
`m` on `σ →₀ ℕ`: comparisons of degrees with their `WithBot` forms, the degree of a monomial
multiple, the cancellation of leading terms by an S-polynomial, the behaviour of leading data
under a change of coefficients, leading data of the weighted homogeneous component containing
the leading monomial, leading data of renamed polynomials, elimination orders and the
lexicographic ones among them, agreement of leading exponents under two monomial orders, and
algebraic independence from leading monomials.

The product `X^a * b`, normalized to leading coefficient one when `b` has a unit leading
coefficient, differs from another such product of the same degree by a monomial multiple of
their S-polynomial. This is the cancellation of leading terms behind Buchberger's criterion.

Let `yᵢ`, `i ∈ σ`, be polynomials in the variables `Xᵢ` over a ring without zero divisors. If the
leading monomial of each `yᵢ` is the variable `Xᵢ`, then the `yᵢ` are algebraically independent:
the image of a monomial `c X^d` under `Xᵢ ↦ yᵢ` has leading monomial `X^d`, so the images of the
distinct monomials of a nonzero polynomial have distinct leading monomials and cannot cancel.

This is the triangularity argument for a family such as `yₙ = cₙ Xₙ + qₙ(X₁, …, Xₙ₋₁)` with
`cₙ ≠ 0`, ordered lexicographically with the variables of larger index more significant, as for
the images of the generators of the Lazard ring in a polynomial ring.

## Main results

* `MonomialOrder.degree_eq_of_forall_lt`, `MonomialOrder.degree_eq_of_forall_mem_lt`: strict
  comparisons preserving the leading exponent, including comparisons on a set containing the
  support and original leading exponent.
* `MonomialOrder.leadingCoeff_eq_of_degree_eq`, `MonomialOrder.leadingTerm_eq_of_degree_eq`,
  `MonomialOrder.sPolynomial_eq_of_degree_eq`: orders agreeing on leading exponents also agree
  on the corresponding leading coefficients, leading terms and S-polynomials.
* `MonomialOrder.toWithBotSyn_withBotDegree_le_toSyn_degree`: the `WithBot` degree of a polynomial
  is at most its degree.
* `MonomialOrder.withBotDegree_sub_lt`: if `q` has degree at most that of `f ≠ 0` and the same
  coefficient of `X^(deg f)`, then `f - q` has smaller degree than `f`.
* `MvPolynomial.monomial_mem_iff_monomial_one_mem`: a set closed under scalar multiplication
  contains `c X^a` for a unit `c` if and only if it contains `X^a`.
* `MonomialOrder.leadingTerm_mem_iff`: a set closed under scalar multiplication contains the
  leading term of a polynomial with unit leading coefficient if and only if it contains its
  leading monomial.
* `MonomialOrder.toSyn_degree_monomial_mul_le`: `c X^a * b` has degree at most `a + deg b`.
* `MonomialOrder.monomial_one_mul_sub_smul_eq_monomial_mul_sPolynomial`: if `b₀` has a unit
  leading coefficient, then `X^a * b` minus `lc b` times the product of `b₀` of the same degree
  normalized to leading coefficient one is a monomial multiple of the S-polynomial
  `m.sPolynomial b b₀`.
* `MonomialOrder.degree_map_of_injective`, `MonomialOrder.leadingCoeff_map_of_injective`,
  `MonomialOrder.leadingTerm_map_of_injective`, `MonomialOrder.sPolynomial_map_of_injective`: an
  injective coefficient map `φ` preserves leading monomials and commutes with leading
  coefficients, leading terms and S-polynomials.
* `MonomialOrder.leadingTerm_weightedHomogeneousComponent_weight_degree`: the weighted
  homogeneous component of `f` containing its leading monomial has the leading term of `f`.
* `MonomialOrder.degree_rename`, `MonomialOrder.leadingCoeff_rename` and
  `MonomialOrder.leadingTerm_rename`: renaming the variables along a relabeling which carries one
  monomial order to another commutes with leading monomials, coefficients and terms; such a
  relabeling is injective by `MonomialOrder.injective_of_forall_toSyn_le_iff`.
* `MonomialOrder.exists_rename_eq_of_coe_support_degree_subset`: for an elimination order, a
  polynomial whose leading monomial only involves the variables `e τ` is a renamed polynomial.
* `MonomialOrder.coe_support_subset_of_lex_le`: monomials supported in an upper set of variables
  form a lower set for the lexicographic order.
* `MonomialOrder.algebraicIndependent_of_degree_eq_single`: polynomials `yᵢ` whose leading
  monomial is `Xᵢ` are algebraically independent.
-/


open MvPolynomial

/-- A set of polynomials closed under scalar multiplication (for example a submodule or a
subalgebra) contains a monomial with unit coefficient if and only if it contains the
corresponding monomial with coefficient one. -/
theorem MvPolynomial.monomial_mem_iff_monomial_one_mem {σ R S : Type*} [CommSemiring R]
    [SetLike S (MvPolynomial σ R)] [SMulMemClass S R (MvPolynomial σ R)]
    {a : σ →₀ ℕ} {c : R} (C : S) (hc : IsUnit c) :
    monomial a c ∈ C ↔ monomial a 1 ∈ C := by
  obtain ⟨u, rfl⟩ := hc
  have h : monomial a (u : R) = (u : R) • monomial a 1 := by simp [smul_monomial]
  rw [h]
  refine ⟨fun hu => ?_, SMulMemClass.smul_mem _⟩
  simpa [smul_smul] using SMulMemClass.smul_mem ((u⁻¹ : Rˣ) : R) hu

namespace MonomialOrder

variable {σ R : Type*} (m : MonomialOrder σ)

/-- Two monomial orders give the same leading exponent of `f` if every other exponent in its
support remains strictly below its original leading exponent. -/
theorem degree_eq_of_forall_lt [CommSemiring R] (n : MonomialOrder σ)
    (f : MvPolynomial σ R)
    (h : ∀ a ∈ f.support, a ≠ m.degree f → a ≺[n] m.degree f) :
    n.degree f = m.degree f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  apply n.toSyn.injective
  refine le_antisymm (n.degree_le_iff.2 fun a ha ↦ ?_)
    (n.le_degree (m.degree_mem_support hf))
  rcases eq_or_ne a (m.degree f) with rfl | hne
  · exact le_rfl
  · exact (h a ha hne).le

/-- Orders preserving strict comparisons on a set containing the support and original leading
exponent of a polynomial give it the same leading exponent. -/
theorem degree_eq_of_forall_mem_lt [CommSemiring R] (n : MonomialOrder σ)
    (f : MvPolynomial σ R) {s : Set (σ →₀ ℕ)}
    (h : ∀ a ∈ s, ∀ b ∈ s, a ≺[m] b → a ≺[n] b)
    (hf : ↑f.support ⊆ s) (hd : m.degree f ∈ s) : n.degree f = m.degree f := by
  apply m.degree_eq_of_forall_lt n f
  intro a ha hne
  exact h a (hf ha) _ hd (lt_of_le_of_ne (m.le_degree ha) (m.toSyn.injective.ne hne))

/-- Orders agreeing on the leading exponent of a polynomial agree on its leading coefficient. -/
theorem leadingCoeff_eq_of_degree_eq [CommSemiring R] (n : MonomialOrder σ)
    {f : MvPolynomial σ R} (h : n.degree f = m.degree f) :
    n.leadingCoeff f = m.leadingCoeff f := by
  simp only [leadingCoeff, h]

/-- Orders agreeing on the leading exponent of a polynomial agree on its leading term. -/
theorem leadingTerm_eq_of_degree_eq [CommSemiring R] (n : MonomialOrder σ)
    {f : MvPolynomial σ R} (h : n.degree f = m.degree f) :
    n.leadingTerm f = m.leadingTerm f := by
  rw [leadingTerm, leadingTerm, h, m.leadingCoeff_eq_of_degree_eq n h]

/-- Orders agreeing on the leading exponents of two polynomials give the same S-polynomial. -/
theorem sPolynomial_eq_of_degree_eq [CommRing R] (n : MonomialOrder σ)
    {f g : MvPolynomial σ R} (hf : n.degree f = m.degree f) (hg : n.degree g = m.degree g) :
    n.sPolynomial f g = m.sPolynomial f g := by
  simp only [sPolynomial, hf, hg, m.leadingCoeff_eq_of_degree_eq n hf,
    m.leadingCoeff_eq_of_degree_eq n hg]

/-- The `WithBot` degree of a polynomial is at most its degree. -/
theorem toWithBotSyn_withBotDegree_le_toSyn_degree [CommSemiring R] (p : MvPolynomial σ R) :
    m.toWithBotSyn (m.withBotDegree p) ≤ m.toSyn (m.degree p) := by
  classical
  rw [withBotDegree_eq]
  split_ifs <;> simp [toWithBotSyn_apply_coe]

/-- If `q` has degree at most that of `f ≠ 0` and the same coefficient of `X^(deg f)`, then
`f - q` has smaller degree than `f`. -/
theorem withBotDegree_sub_lt [CommRing R] {f q : MvPolynomial σ R} (hf : f ≠ 0)
    (hq : m.toWithBotSyn (m.withBotDegree q) ≤ m.toWithBotSyn (m.withBotDegree f))
    (hqf : q.coeff (m.degree f) = m.leadingCoeff f) :
    m.toWithBotSyn (m.withBotDegree (f - q)) < m.toWithBotSyn (m.withBotDegree f) := by
  refine lt_of_le_of_ne ?_ fun heq ↦ ?_
  · simpa [sub_eq_add_neg] using
      (m.withBotDegree_add_le f (-q)).trans (max_le le_rfl (by rwa [withBotDegree_neg]))
  rw [EmbeddingLike.apply_eq_iff_eq, withBotDegree_eq_withBotDegree_iff] at heq
  have := m.degree_mem_support fun h0 ↦ hf (heq.2.1 h0)
  rw [heq.1, mem_support_iff, coeff_sub, hqf, leadingCoeff, sub_self] at this
  exact this rfl

/-- A monomial multiple `c X^a * b` has degree at most `a + deg b`. -/
theorem toSyn_degree_monomial_mul_le [CommSemiring R] (a : σ →₀ ℕ) (c : R)
    (b : MvPolynomial σ R) : m.toSyn (m.degree (monomial a c * b)) ≤ m.toSyn (a + m.degree b) := by
  rw [map_add]
  exact m.toSyn_degree_mul_le.trans (by gcongr; exact m.degree_monomial_le c)

/-- A set of polynomials closed under scalar multiplication (for example a submodule or a
subalgebra) contains the leading term of a polynomial with unit leading coefficient if and only
if it contains its leading monomial. -/
theorem leadingTerm_mem_iff [CommSemiring R] {S : Type*} [SetLike S (MvPolynomial σ R)]
    [SMulMemClass S R (MvPolynomial σ R)] {f : MvPolynomial σ R} (C : S)
    (hf : IsUnit (m.leadingCoeff f)) :
    m.leadingTerm f ∈ C ↔ monomial (m.degree f) 1 ∈ C := by
  rw [leadingTerm, monomial_mem_iff_monomial_one_mem C hf]

/-- **Cancellation of leading terms by an S-polynomial.** If `b₀` has unit leading coefficient
`u₀` and `deg b₀ ≤ a + deg b`, the difference between `X^a * b` and `lc b` times the normalized
product `X^(a + deg b - deg b₀) * b₀ / lc b₀` is `X^(a + deg b - L) / lc b₀ * S(b, b₀)`, where
`L = deg b ⊔ deg b₀`. -/
theorem monomial_one_mul_sub_smul_eq_monomial_mul_sPolynomial [CommRing R] {a : σ →₀ ℕ}
    {b b₀ : MvPolynomial σ R} (hb₀ : m.degree b₀ ≤ a + m.degree b) (u₀ : Rˣ)
    (hu₀ : (u₀ : R) = m.leadingCoeff b₀) :
    monomial a 1 * b -
        m.leadingCoeff b • (monomial (a + m.degree b - m.degree b₀) ((u₀⁻¹ : Rˣ) : R) * b₀) =
      monomial (a + m.degree b - m.degree b ⊔ m.degree b₀) ((u₀⁻¹ : Rˣ) : R) *
        m.sPolynomial b b₀ := by
  have hL : m.degree b ⊔ m.degree b₀ ≤ a + m.degree b := sup_le le_add_self hb₀
  -- The exponents of the two summands of the right-hand side.
  have e₁ : a + m.degree b - m.degree b ⊔ m.degree b₀ + (m.degree b ⊔ m.degree b₀ - m.degree b) =
      a := by
    rw [tsub_add_tsub_cancel hL le_sup_left, add_tsub_cancel_right]
  have e₂ : a + m.degree b - m.degree b ⊔ m.degree b₀ + (m.degree b ⊔ m.degree b₀ - m.degree b₀) =
      a + m.degree b - m.degree b₀ :=
    tsub_add_tsub_cancel hL le_sup_right
  -- The coefficient of the first summand.
  have hc : ((u₀⁻¹ : Rˣ) : R) * m.leadingCoeff b₀ = 1 := by rw [← hu₀, Units.inv_mul]
  simp only [sPolynomial_def, mul_sub, ← mul_assoc, monomial_mul_monomial, smul_eq_C_mul,
    C_mul_monomial, e₁, e₂, hc, mul_comm (m.leadingCoeff b)]

section Map

variable {S : Type*}

section CommSemiring

variable [CommSemiring R] [CommSemiring S] (φ : R →+* S) {f : MvPolynomial σ R}

/-- A coefficient map that does not kill the leading coefficient preserves the leading monomial. -/
theorem degree_map_of_leadingCoeff_ne_zero (h : φ (m.leadingCoeff f) ≠ 0) :
    m.degree (map φ f) = m.degree f := by
  have hmem : m.degree f ∈ (map φ f).support := by
    rwa [mem_support_iff, coeff_map]
  exact m.toSyn.injective <| le_antisymm
    (m.degree_le_iff.2 fun _ hc ↦ m.le_degree (support_map_subset φ f hc)) (m.le_degree hmem)

/-- A coefficient map that does not kill the leading coefficient maps it to the leading
coefficient of the image. -/
theorem leadingCoeff_map_of_leadingCoeff_ne_zero (h : φ (m.leadingCoeff f) ≠ 0) :
    m.leadingCoeff (map φ f) = φ (m.leadingCoeff f) := by
  rw [leadingCoeff, degree_map_of_leadingCoeff_ne_zero m φ h, coeff_map, leadingCoeff]

variable {φ}

/-- An injective coefficient map preserves the leading monomial. -/
theorem degree_map_of_injective (hφ : Function.Injective φ) (f : MvPolynomial σ R) :
    m.degree (map φ f) = m.degree f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  exact m.degree_map_of_leadingCoeff_ne_zero φ
    ((map_ne_zero_iff φ hφ).2 (m.leadingCoeff_ne_zero_iff.2 hf))

/-- An injective coefficient map preserves the `WithBot` degree. -/
theorem withBotDegree_map_of_injective (hφ : Function.Injective φ) (f : MvPolynomial σ R) :
    m.withBotDegree (map φ f) = m.withBotDegree f := by
  classical
  simp [withBotDegree_eq, m.degree_map_of_injective hφ, map_eq_zero_iff _ (map_injective φ hφ)]

/-- An injective coefficient map sends the leading coefficient to the leading coefficient of the
image. -/
theorem leadingCoeff_map_of_injective (hφ : Function.Injective φ) (f : MvPolynomial σ R) :
    m.leadingCoeff (map φ f) = φ (m.leadingCoeff f) := by
  rw [leadingCoeff, m.degree_map_of_injective hφ, coeff_map, leadingCoeff]

/-- An injective coefficient map sends the leading term to the leading term of the image. -/
theorem leadingTerm_map_of_injective (hφ : Function.Injective φ) (f : MvPolynomial σ R) :
    m.leadingTerm (map φ f) = map φ (m.leadingTerm f) := by
  rw [leadingTerm, leadingTerm, map_monomial, m.degree_map_of_injective hφ,
    m.leadingCoeff_map_of_injective hφ]

end CommSemiring

/-- An injective coefficient map sends the S-polynomial of `f` and `g` to the S-polynomial of
their images. -/
theorem sPolynomial_map_of_injective [CommRing R] [CommRing S] {φ : R →+* S}
    (hφ : Function.Injective φ) (f g : MvPolynomial σ R) :
    m.sPolynomial (map φ f) (map φ g) = map φ (m.sPolynomial f g) := by
  simp only [sPolynomial, map_sub, map_mul, map_monomial, m.degree_map_of_injective hφ,
    m.leadingCoeff_map_of_injective hφ]

end Map

section WeightedHomogeneous

open Finsupp

variable {M : Type*} [AddCommMonoid M] [CommSemiring R] (w : σ → M)

/-- The weighted homogeneous component of `f` whose weight is that of the leading monomial of `f`
has the same leading monomial as `f`. -/
@[simp]
theorem degree_weightedHomogeneousComponent_weight_degree (f : MvPolynomial σ R) :
    m.degree (weightedHomogeneousComponent w (weight w (m.degree f)) f) = m.degree f := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hsupp := support_weightedHomogeneousComponent (w := w) (weight w (m.degree f)) f
  refine m.toSyn.injective (le_antisymm (m.degree_le_iff.2 fun c hc ↦ ?_) (m.le_degree ?_))
  · rw [hsupp] at hc
    exact m.le_degree (Finset.mem_filter.1 hc).1
  · rw [hsupp]
    exact Finset.mem_filter.2 ⟨m.degree_mem_support hf, rfl⟩

/-- The weighted homogeneous component of `f` containing its leading monomial has the same leading
coefficient as `f`. -/
@[simp]
theorem leadingCoeff_weightedHomogeneousComponent_weight_degree (f : MvPolynomial σ R) :
    m.leadingCoeff (weightedHomogeneousComponent w (weight w (m.degree f)) f) =
      m.leadingCoeff f := by
  classical
  simp [leadingCoeff, coeff_weightedHomogeneousComponent]

/-- The weighted homogeneous component of `f` containing its leading monomial has the same leading
term as `f`. -/
@[simp]
theorem leadingTerm_weightedHomogeneousComponent_weight_degree (f : MvPolynomial σ R) :
    m.leadingTerm (weightedHomogeneousComponent w (weight w (m.degree f)) f) =
      m.leadingTerm f := by
  simp [leadingTerm]

/-- The weighted homogeneous component of `f` containing its leading monomial is weighted
homogeneous of the weight of its own leading monomial. -/
theorem isWeightedHomogeneous_weightedHomogeneousComponent_weight_degree (f : MvPolynomial σ R) :
    IsWeightedHomogeneous w (weightedHomogeneousComponent w (weight w (m.degree f)) f)
      (weight w (m.degree (weightedHomogeneousComponent w (weight w (m.degree f)) f))) := by
  rw [degree_weightedHomogeneousComponent_weight_degree]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

end WeightedHomogeneous

section Rename

variable {τ : Type*} [CommSemiring R] {m} {m' : MonomialOrder τ} {e : τ → σ}

/-- A relabeling of variables which carries the monomial order `m'` to `m` is injective. -/
theorem injective_of_forall_toSyn_le_iff
    (hm : ∀ a b : τ →₀ ℕ, a ≼[m'] b ↔ a.mapDomain e ≼[m] b.mapDomain e) :
    Function.Injective e := by
  intro i j hij
  -- The two variables `X i`, `X j` are renamed to the same variable, so neither exceeds the other.
  have hsingle : m.toSyn ((Finsupp.single i 1).mapDomain e) =
      m.toSyn ((Finsupp.single j 1).mapDomain e) := by
    simp [hij]
  have h := m'.toSyn.injective <| le_antisymm ((hm _ _).2 hsingle.le) ((hm _ _).2 hsingle.ge)
  simpa [Finsupp.single_left_inj] using h

/-- Renaming the variables along a relabeling which carries the monomial order `m'` to `m` renames
the leading monomial. -/
theorem degree_rename (hm : ∀ a b : τ →₀ ℕ, a ≼[m'] b ↔ a.mapDomain e ≼[m] b.mapDomain e)
    (p : MvPolynomial τ R) : m.degree (rename e p) = (m'.degree p).mapDomain e := by
  classical
  have he := injective_of_forall_toSyn_le_iff hm
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  refine m.toSyn.injective (le_antisymm (m.degree_le_iff.2 fun c hc ↦ ?_) (m.le_degree ?_))
  · rw [support_rename_of_injective he, Finset.mem_image] at hc
    obtain ⟨a, ha, rfl⟩ := hc
    exact (hm _ _).1 (m'.le_degree ha)
  · rw [support_rename_of_injective he]
    exact Finset.mem_image_of_mem _ (m'.degree_mem_support hp)

/-- Renaming the variables along a relabeling which carries the monomial order `m'` to `m`
preserves the leading coefficient. -/
theorem leadingCoeff_rename (hm : ∀ a b : τ →₀ ℕ, a ≼[m'] b ↔ a.mapDomain e ≼[m] b.mapDomain e)
    (p : MvPolynomial τ R) : m.leadingCoeff (rename e p) = m'.leadingCoeff p := by
  rw [leadingCoeff, degree_rename hm,
    coeff_rename_mapDomain _ (injective_of_forall_toSyn_le_iff hm), leadingCoeff]

/-- Renaming the variables along a relabeling which carries the monomial order `m'` to `m`
renames the leading term. -/
theorem leadingTerm_rename (hm : ∀ a b : τ →₀ ℕ, a ≼[m'] b ↔ a.mapDomain e ≼[m] b.mapDomain e)
    (p : MvPolynomial τ R) : m.leadingTerm (rename e p) = rename e (m'.leadingTerm p) := by
  rw [leadingTerm, leadingTerm, degree_rename hm, leadingCoeff_rename hm, rename_monomial]

/-- For an elimination order `m` for the variables `e τ`, that is, one in which every monomial
below a monomial in these variables is again a monomial in these variables, a polynomial whose
leading monomial only involves the variables `e τ` is the renaming of a polynomial in the
variables `τ`. -/
theorem exists_rename_eq_of_coe_support_degree_subset
    (helim : ∀ a b : σ →₀ ℕ, a ≼[m] b → ↑b.support ⊆ Set.range e → ↑a.support ⊆ Set.range e)
    (he : Function.Injective e) {g : MvPolynomial σ R}
    (hg : ↑(m.degree g).support ⊆ Set.range e) : ∃ g' : MvPolynomial τ R, rename e g' = g := by
  classical
  refine exists_rename_eq_of_vars_subset_range g e he fun i hi ↦ ?_
  obtain ⟨d, hd, hid⟩ := (mem_vars_iff_mem_support i).1 hi
  exact helim d _ (m.le_degree hd) hg hid

end Rename

section Lex

/-- For the lexicographic order, the monomials supported in an upper set of variables form a
lower set: with the antitone variable convention these are the smallest variables. -/
theorem coe_support_subset_of_lex_le [LinearOrder σ] [WellFoundedGT σ] {s : Set σ}
    (hs : IsUpperSet s) {a b : σ →₀ ℕ} (hab : a ≼[lex] b) (hb : ↑b.support ⊆ s) :
    ↑a.support ⊆ s := by
  intro j hj
  by_contra hjs
  rcases eq_or_ne a b with rfl | hne
  · exact hjs (hb hj)
  -- `a < b` first differs from `b` at some `i` with `0 ≤ a i < b i`, so `i ∈ s`; since `j ∉ s`,
  -- `j < i`, and then `a j = b j = 0`.
  obtain ⟨i, hi, hlt⟩ := Finsupp.Lex.lt_iff.1 <| lex_lt_iff.1 <|
    lt_of_le_of_ne hab (lex.toSyn.injective.ne hne)
  have hbi : i ∈ s := hb (Finsupp.mem_support_iff.2 (Nat.zero_lt_of_lt hlt).ne')
  have hji : j < i := lt_of_not_ge fun hij ↦ hjs (hs hij hbi)
  have hbj : b j = 0 := Finsupp.notMem_support_iff.1 fun h ↦ hjs (hb h)
  exact (Finsupp.mem_support_iff.1 hj) ((hi j hji).trans hbj)

end Lex

variable [CommRing R] [NoZeroDivisors R]

/-- **Algebraic independence from leading monomials.** Over a ring without zero divisors, a family
`yᵢ` of polynomials in the variables `Xᵢ` whose leading monomial for a monomial order is `Xᵢ` is
algebraically independent. -/
theorem algebraicIndependent_of_degree_eq_single {y : σ → MvPolynomial σ R}
    (hy : ∀ i, m.degree (y i) = Finsupp.single i 1) : AlgebraicIndependent R y := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact algebraicIndependent_iff_injective_aeval.2 fun _ _ _ ↦ Subsingleton.elim _ _
  have hy0 (i : σ) : y i ≠ 0 := fun h ↦ by
    simpa [h] using congrArg (fun d ↦ d i) (hy i)
  have hne (d : σ →₀ ℕ) : (d.prod fun i k ↦ y i ^ k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ ↦ pow_ne_zero _ (hy0 i)
  -- The image `c ∏ yᵢ ^ dᵢ` of a monomial `c X^d` with `c ≠ 0` has leading monomial `X^d`.
  have hterm {c : R} (hc : c ≠ 0) (d : σ →₀ ℕ) : m.degree (aeval y (monomial d c)) = d := by
    rw [aeval_monomial, algebraMap_eq, m.degree_mul (C_ne_zero.2 hc) (hne d), m.degree_C,
      zero_add, Finsupp.prod, m.degree_prod fun i _ ↦ pow_ne_zero _ (hy0 i)]
    simp_rw [m.degree_pow, hy, Finsupp.smul_single, smul_eq_mul, mul_one]
    exact d.sum_single
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro p hp
  by_contra hp0
  rw [p.as_sum, map_sum] at hp
  -- The images of the monomials of `p` have pairwise distinct leading monomials, so their sum is
  -- nonzero.
  refine AddMonoidAlgebra.sum_ne_zero_of_injOn_supDegree (D := m.toSyn)
    (support_nonempty.2 hp0) (fun d hd ↦ ?_) (fun d hd e he hde ↦ ?_) hp
  · rw [aeval_monomial, algebraMap_eq]
    exact mul_ne_zero (C_ne_zero.2 (mem_support_iff.1 hd)) (hne d)
  · have key (d : σ →₀ ℕ) (hd : d ∈ p.support) :
        AddMonoidAlgebra.supDegree m.toSyn (aeval y (monomial d (p.coeff d))) = m.toSyn d := by
      -- `m.degree` is defined as the supremum `AddMonoidAlgebra.supDegree m.toSyn`, read back
      -- through `m.toSyn`.
      have h : m.toSyn (m.degree (aeval y (monomial d (p.coeff d)))) =
          AddMonoidAlgebra.supDegree m.toSyn (aeval y (monomial d (p.coeff d))) := by
        rw [degree, AddEquiv.apply_symm_apply]
        rfl
      rw [← h, hterm (mem_support_iff.1 hd)]
    have hde' :
        AddMonoidAlgebra.supDegree m.toSyn (aeval y (monomial d (p.coeff d))) =
          AddMonoidAlgebra.supDegree m.toSyn (aeval y (monomial e (p.coeff e))) := hde
    rw [key d hd, key e he] at hde'
    exact m.toSyn.injective hde'

end MonomialOrder

end

section
/- Source body: remote_vendor_GroebnerBasic.lean -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Remainders and Gröbner bases

Let `m` be a monomial order on `σ →₀ ℕ`. This file defines remainders on division by a set of
multivariate polynomials, and Gröbner bases of an ideal, and proves that remainders on division by
a Gröbner basis decide ideal membership.

* `MonomialOrder.IsRemainder m f B r`: `r` is a remainder of `f` on division by `B`, i.e.
  `f = ∑ g_b * b + r` where each product `g_b * b` has degree at most that of `f`, and no monomial
  of `r` is divisible by the leading monomial of a nonzero `b ∈ B`. The degree condition is
  stated with `MonomialOrder.withBotDegree`, so that the zero polynomial has degree `⊥`, and as
  the inequality `deg b + deg g_b ≤ deg f`; the remainder condition only concerns divisibility,
  not a comparison of degrees.
* `MonomialOrder.IsGroebnerBasis m G I`: `G` is a subset of the ideal `I` whose leading terms
  span the same ideal as the leading terms of all elements of `I`.

## Main results

* `MonomialOrder.exists_isRemainder`: remainders exist when every nonzero divisor has a unit
  leading coefficient; this is `MonomialOrder.div_set`.
* `MonomialOrder.IsGroebnerBasis.exists_degree_le_degree`: the leading monomial of every nonzero
  element of `I` is divisible by the leading monomial of a nonzero element of a Gröbner basis.
* `MonomialOrder.isGroebnerBasis_iff_forall_exists_degree_le_degree`: the converse, for a family
  whose nonzero members have unit leading coefficients.
* `MonomialOrder.IsGroebnerBasis.image_leadingTerm`: the leading terms of such a Gröbner basis of
  `I` form a Gröbner basis of the ideal of leading terms of `I`.
* `MonomialOrder.IsGroebnerBasis.sub_mem_iff`: for remainders `r₁`, `r₂` of `f₁`, `f₂` on division
  by a Gröbner basis of `I`, `f₁ - f₂ ∈ I` if and only if `r₁ = r₂`. In particular remainders on
  division by a Gröbner basis are unique (`MonomialOrder.IsGroebnerBasis.eq_of_isRemainder`) and
  a remainder vanishes exactly on `I` (`MonomialOrder.IsGroebnerBasis.remainder_eq_zero_iff_mem`).
* `MonomialOrder.IsGroebnerBasis.isRemainder_zero_iff_mem`: `0` is a remainder of `f` on division
  by a Gröbner basis of `I` if and only if `f ∈ I`, whatever the leading coefficients of the basis:
  every element of `I` has a standard representation (Adams–Loustaunau, Theorem 4.1.12).
* `MonomialOrder.IsGroebnerBasis.ideal_eq_span`: a Gröbner basis generates its ideal.
* `MonomialOrder.isGroebnerBasis_iff_isRemainder_zero`: `G ⊆ I` is a Gröbner basis of `I` if and
  only if every element of `I` has remainder `0` on division by `G`.

None of these results assume that the coefficients form a field: the statements needing division
assume that the nonzero members of the divisor set have unit leading coefficients, which over a
field is discharged by `MonomialOrder.isUnit_leadingCoeff`.

## References

The definitions `IsRemainder` and `IsGroebnerBasis` are those of Junyu Guo and Hao Shen in
Mathlib pull request 29203, upstreamed from the WuProver Gröbner basis project.

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 2, §§5–6.
* W. W. Adams, P. Loustaunau, *An Introduction to Gröbner Bases*, Graduate Studies in
  Mathematics 3, American Mathematical Society, 1994, §4.1: Gröbner bases over rings and standard
  representations.
-/


namespace MonomialOrder

open MvPolynomial

variable {σ R : Type*} (m : MonomialOrder σ)

section CommSemiring

variable [CommSemiring R]

/-- `r` is a remainder of `f` on division by the set `B` for the monomial order `m`: there is a
finitely supported family `g : B →₀ MvPolynomial σ R` such that

1. `f = ∑ g_b * b + r`;
2. for each `b ∈ B`, `deg b + deg g_b ≤ deg f`, degrees being taken in `WithBot` so that the zero
   polynomial has degree `⊥`;
3. no monomial of `r` is divisible by the leading monomial of a nonzero `b ∈ B`. -/
def IsRemainder (f : MvPolynomial σ R) (B : Set (MvPolynomial σ R)) (r : MvPolynomial σ R) :
    Prop :=
  (∃ g : B →₀ MvPolynomial σ R,
    f = Finsupp.linearCombination _ (fun b : B ↦ (b : MvPolynomial σ R)) g + r ∧
    ∀ b : B, m.toWithBotSyn (m.withBotDegree (b : MvPolynomial σ R)) +
      m.toWithBotSyn (m.withBotDegree (g b)) ≤ m.toWithBotSyn (m.withBotDegree f)) ∧
  ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ m.degree b ≤ c

/-- A subset `G` of an ideal `I` is a Gröbner basis of `I` for the monomial order `m` if the
leading terms of the elements of `G` span the same ideal as the leading terms of all elements
of `I`. -/
def IsGroebnerBasis (G : Set (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R)) : Prop :=
  G ⊆ I ∧ Ideal.span (m.leadingTerm '' I) = Ideal.span (m.leadingTerm '' G)

variable {m} {f r : MvPolynomial σ R} {B G G' : Set (MvPolynomial σ R)}
  {I : Ideal (MvPolynomial σ R)}

/-- Unfolding lemma for `MonomialOrder.IsRemainder`. -/
theorem isRemainder_iff : m.IsRemainder f B r ↔
    (∃ g : B →₀ MvPolynomial σ R,
      f = Finsupp.linearCombination _ (fun b : B ↦ (b : MvPolynomial σ R)) g + r ∧
      ∀ b : B, m.toWithBotSyn (m.withBotDegree (b : MvPolynomial σ R)) +
        m.toWithBotSyn (m.withBotDegree (g b)) ≤ m.toWithBotSyn (m.withBotDegree f)) ∧
    ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ m.degree b ≤ c :=
  Iff.rfl

/-- The division representation of a remainder: `f = ∑ g_b * b + r` with
`deg b + deg g_b ≤ deg f` for each `b ∈ B`. -/
theorem IsRemainder.exists_linearCombination (h : m.IsRemainder f B r) :
    ∃ g : B →₀ MvPolynomial σ R,
      f = Finsupp.linearCombination _ (fun b : B ↦ (b : MvPolynomial σ R)) g + r ∧
      ∀ b : B, m.toWithBotSyn (m.withBotDegree (b : MvPolynomial σ R)) +
        m.toWithBotSyn (m.withBotDegree (g b)) ≤ m.toWithBotSyn (m.withBotDegree f) :=
  h.1

/-- No monomial of a remainder is divisible by the leading monomial of a nonzero divisor. -/
theorem IsRemainder.not_degree_le (h : m.IsRemainder f B r) {c : σ →₀ ℕ} (hc : c ∈ r.support)
    {b : MvPolynomial σ R} (hb : b ∈ B) (hb0 : b ≠ 0) : ¬ m.degree b ≤ c :=
  h.2 c hc b hb hb0

/-- Unfolding lemma for `MonomialOrder.IsGroebnerBasis`. -/
theorem isGroebnerBasis_iff : m.IsGroebnerBasis G I ↔
    G ⊆ I ∧ Ideal.span (m.leadingTerm '' I) = Ideal.span (m.leadingTerm '' G) :=
  Iff.rfl

/-- A subset of `I` whose leading terms span the ideal of leading terms of `I` is a Gröbner basis
of `I`. -/
theorem IsGroebnerBasis.mk (hGI : G ⊆ I)
    (hspan : Ideal.span (m.leadingTerm '' I) = Ideal.span (m.leadingTerm '' G)) :
    m.IsGroebnerBasis G I :=
  ⟨hGI, hspan⟩

/-- For nonzero `p`, `q` and `f`, the `WithBot` degree bound `deg p + deg q ≤ deg f` used in
`MonomialOrder.IsRemainder` is the corresponding bound on `MonomialOrder.degree`. -/
theorem toWithBotSyn_withBotDegree_add_le_iff {p q : MvPolynomial σ R} (hp : p ≠ 0) (hq : q ≠ 0)
    (hf : f ≠ 0) :
    m.toWithBotSyn (m.withBotDegree p) + m.toWithBotSyn (m.withBotDegree q) ≤
        m.toWithBotSyn (m.withBotDegree f) ↔
      m.toSyn (m.degree p) + m.toSyn (m.degree q) ≤ m.toSyn (m.degree f) := by
  simp [(m.withBotDegree_eq_coe_degree_iff _).2, toWithBotSyn_apply_coe, ← WithBot.coe_add, *]

/-- The remainders of `0` are exactly `0`. -/
@[simp]
theorem isRemainder_zero_left_iff : m.IsRemainder 0 B r ↔ r = 0 := by
  refine ⟨fun ⟨⟨g, hg, hdeg⟩, _⟩ ↦ ?_, fun hr ↦ ⟨⟨0, by simp [hr], by simp⟩, by simp [hr]⟩⟩
  -- Each product `g b * b` vanishes, since its degree is bounded by the degree `⊥` of `0`.
  have hgb (b : B) : g b • (b : MvPolynomial σ R) = 0 := by
    have := hdeg b
    simp only [withBotDegree_zero, toWithBotSyn_apply_bot, le_bot_iff, WithBot.add_eq_bot,
      toWithBotSyn_apply_eq_bot_iff, withBotDegree_eq_bot_iff] at this
    rcases this with h | h <;> simp [h]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_eq_zero fun b _ ↦ hgb b,
    zero_add] at hg
  exact hg.symm

/-- A polynomial is a remainder of itself on division by `B` exactly when none of its monomials is
divisible by the leading monomial of a nonzero element of `B`. -/
theorem isRemainder_self_iff :
    m.IsRemainder r B r ↔ ∀ c ∈ r.support, ∀ b ∈ B, b ≠ 0 → ¬ m.degree b ≤ c :=
  ⟨And.right, fun h ↦ ⟨⟨0, by simp, by simp⟩, h⟩⟩

/-- If `0` is a remainder of `f` on division by `B`, then the leading term of `f` lies in the ideal
spanned by the leading terms of `B`. -/
theorem leadingTerm_mem_span_leadingTerm_of_isRemainder_zero (h : m.IsRemainder f B 0) :
    m.leadingTerm f ∈ Ideal.span (m.leadingTerm '' B) := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨g, hfg, hdeg⟩ := h.exists_linearCombination
  rw [add_zero, Finsupp.linearCombination_apply, Finsupp.sum] at hfg
  -- `lt f` is the sum of the `deg f` terms of the products `g_b * b`.
  have hlt : m.leadingTerm f = ∑ b ∈ g.support,
      monomial (m.degree f) ((g b * (b : MvPolynomial σ R)).coeff (m.degree f)) := by
    simp_rw [← map_sum, ← coeff_sum, ← smul_eq_mul, ← hfg, leadingTerm, leadingCoeff]
  refine hlt ▸ sum_mem fun b _ ↦ ?_
  by_cases hb : m.degree f ∈ (g b * (b : MvPolynomial σ R)).support
  · have hgb0 : g b ≠ 0 := fun h ↦ by simp [h] at hb
    have hb0 : (b : MvPolynomial σ R) ≠ 0 := fun h ↦ by simp [h] at hb
    -- The degree condition gives `deg b + deg g_b ≤ deg f`, and `deg f` is a monomial of
    -- `g_b * b`, so the two sides are equal and the `deg f` term is `lt g_b * lt b`.
    have hle := (toWithBotSyn_withBotDegree_add_le_iff hb0 hgb0 hf).1 (hdeg b)
    have heq : m.degree f = m.degree (g b) + m.degree (b : MvPolynomial σ R) :=
      m.toSyn.injective <| by
        rw [map_add]
        exact le_antisymm ((m.le_degree hb).trans m.toSyn_degree_mul_le)
          ((add_comm _ _).trans_le hle)
    rw [heq, coeff_mul_of_degree_add, ← monomial_mul_monomial]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨b, b.2, rfl⟩)
  · rw [notMem_support_iff.1 hb, map_zero]
    exact zero_mem _

/-- Every monomial of an element of the ideal spanned by the leading terms of `G` is divisible by
the leading monomial of a nonzero element of `G`. -/
theorem exists_degree_le_of_mem_span_leadingTerm {p : MvPolynomial σ R}
    (hp : p ∈ Ideal.span (m.leadingTerm '' G)) {c : σ →₀ ℕ} (hc : c ∈ p.support) :
    ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ c := by
  have hle : Ideal.span (m.leadingTerm '' G) ≤
      Ideal.span ((fun d ↦ monomial d (1 : R)) '' (m.degree '' (G \ {0}))) := by
    rw [← m.span_leadingTerm_sdiff_singleton_zero, Ideal.span_le, Set.image_subset_iff]
    intro g hg
    rw [Set.mem_preimage, SetLike.mem_coe, ← C_mul_leadingCoeff_monomial_degree]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨m.degree g, ⟨g, hg, rfl⟩, rfl⟩)
  obtain ⟨_, ⟨g, ⟨hgG, hg0⟩, rfl⟩, hgc⟩ := mem_ideal_span_monomial_image.1 (hle hp) c hc
  exact ⟨g, hgG, by simpa using hg0, hgc⟩

/-- If `0` is a remainder of a nonzero `f` on division by `B`, then the leading monomial of `f` is
divisible by the leading monomial of a nonzero element of `B`. -/
theorem exists_degree_le_degree_of_isRemainder_zero (h : m.IsRemainder f B 0) (hf : f ≠ 0) :
    ∃ b ∈ B, b ≠ 0 ∧ m.degree b ≤ m.degree f :=
  exists_degree_le_of_mem_span_leadingTerm (leadingTerm_mem_span_leadingTerm_of_isRemainder_zero h)
    (by rw [m.support_leadingTerm' hf]; exact Finset.mem_singleton_self _)

/-- The coefficient of `X^D` in an element of the ideal spanned by the leading terms of `G` lies in
the ideal of `R` spanned by the leading coefficients of those `g ∈ G` with `deg g ≤ D`. -/
theorem coeff_mem_span_leadingCoeff {p : MvPolynomial σ R}
    (hp : p ∈ Ideal.span (m.leadingTerm '' G)) (D : σ →₀ ℕ) :
    p.coeff D ∈ Ideal.span (m.leadingCoeff '' {g ∈ G | m.degree g ≤ D}) := by
  classical
  induction hp using Submodule.span_induction generalizing D with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    rw [leadingTerm, coeff_monomial]
    split_ifs with h
    · exact Ideal.subset_span ⟨g, ⟨hg, h.le⟩, rfl⟩
    · exact zero_mem _
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem (hx D) (hy D)
  | smul a x _ hx =>
    -- Each term `a_e * x_{e'}` of the `D` coefficient of `a * x` has `e' ≤ D`.
    rw [smul_eq_mul, coeff_mul]
    refine sum_mem fun e he ↦ Ideal.mul_mem_left _ _ <|
      Ideal.span_mono (Set.image_mono ?_) (hx e.2)
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at he
    exact fun g hg ↦ ⟨hg.1, hg.2.trans (he ▸ le_add_self)⟩

/-- A Gröbner basis of `I` is contained in `I`. -/
theorem IsGroebnerBasis.subset (h : m.IsGroebnerBasis G I) : G ⊆ I :=
  h.1

/-- The leading terms of a Gröbner basis of `I` span the ideal of leading terms of `I`. -/
theorem IsGroebnerBasis.span_leadingTerm_image (h : m.IsGroebnerBasis G I) :
    Ideal.span (m.leadingTerm '' I) = Ideal.span (m.leadingTerm '' G) :=
  h.2

/-- An ideal is a Gröbner basis of itself. -/
theorem isGroebnerBasis_self (I : Ideal (MvPolynomial σ R)) : m.IsGroebnerBasis (I : Set _) I :=
  .mk subset_rfl rfl

/-- Adjoining further elements of `I` to a Gröbner basis of `I` gives a Gröbner basis of `I`. -/
theorem IsGroebnerBasis.mono (h : m.IsGroebnerBasis G I) (hGG' : G ⊆ G') (hG'I : G' ⊆ I) :
    m.IsGroebnerBasis G' I :=
  .mk hG'I <| le_antisymm
    (h.span_leadingTerm_image.le.trans (Ideal.span_mono (Set.image_mono hGG')))
    (Ideal.span_mono (Set.image_mono hG'I))

/-- Removing `0` does not change whether a set is a Gröbner basis. -/
@[simp]
theorem isGroebnerBasis_sdiff_singleton_zero :
    m.IsGroebnerBasis (G \ {0}) I ↔ m.IsGroebnerBasis G I := by
  simp only [isGroebnerBasis_iff, m.span_leadingTerm_sdiff_singleton_zero,
    Set.sdiff_singleton_subset_iff, Set.insert_eq_of_mem (show (0 : MvPolynomial σ R) ∈ (I : Set _)
      from I.zero_mem)]

/-- The leading monomial of every nonzero element of `I` is divisible by the leading monomial of a
nonzero element of a Gröbner basis of `I`. -/
theorem IsGroebnerBasis.exists_degree_le_degree (h : m.IsGroebnerBasis G I)
    {p : MvPolynomial σ R} (hp : p ∈ I) (hp0 : p ≠ 0) :
    ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ m.degree p := by
  refine exists_degree_le_of_mem_span_leadingTerm
    (h.span_leadingTerm_image ▸ Ideal.subset_span ⟨p, hp, rfl⟩ : m.leadingTerm p ∈ _) ?_
  rw [m.support_leadingTerm' hp0]
  exact Finset.mem_singleton_self _

/-- No monomial of a remainder on division by a Gröbner basis of `I` is divisible by the leading
monomial of a nonzero element of `I`. -/
theorem IsGroebnerBasis.not_degree_le_of_isRemainder (h : m.IsGroebnerBasis G I)
    (hr : m.IsRemainder f G r) {c : σ →₀ ℕ} (hc : c ∈ r.support) {p : MvPolynomial σ R}
    (hp : p ∈ I) (hp0 : p ≠ 0) : ¬ m.degree p ≤ c := fun hle ↦
  let ⟨_, hg, hg0, hgp⟩ := h.exists_degree_le_degree hp hp0
  hr.not_degree_le hc hg hg0 (hgp.trans hle)

/-- A subset `G` of `I` whose nonzero members have unit leading coefficients is a Gröbner basis of
`I` if and only if the leading monomial of every nonzero element of `I` is divisible by the
leading monomial of a nonzero element of `G`. -/
theorem isGroebnerBasis_iff_forall_exists_degree_le_degree
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis G I ↔
      G ⊆ I ∧ ∀ p ∈ I, p ≠ 0 → ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ m.degree p := by
  refine ⟨fun h ↦ ⟨h.subset, fun p hp hp0 ↦ h.exists_degree_le_degree hp hp0⟩,
    fun ⟨hGI, hdeg⟩ ↦ .mk hGI (le_antisymm ?_ (Ideal.span_mono (Set.image_mono hGI)))⟩
  rw [Ideal.span_le, Set.image_subset_iff]
  intro p hp
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  obtain ⟨g, hgG, hg0, hgp⟩ := hdeg p hp hp0
  -- `lt p = (lc p / lc g) X^(deg p - deg g) * lt g`.
  have hu := hG g hgG hg0
  have hlt : m.leadingTerm p = monomial (m.degree p - m.degree g)
      (m.leadingCoeff p * ↑hu.unit⁻¹) * m.leadingTerm g := by
    simp [leadingTerm, monomial_mul_monomial, tsub_add_cancel_of_le hgp, mul_assoc]
  rw [Set.mem_preimage, SetLike.mem_coe, hlt]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨g, hgG, rfl⟩)

/-- If the nonzero members of `G` have unit leading coefficients, then so do the nonzero leading
terms of members of `G`. -/
theorem isUnit_leadingCoeff_of_mem_image_leadingTerm
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    ∀ p ∈ m.leadingTerm '' G, p ≠ 0 → IsUnit (m.leadingCoeff p) := by
  rintro _ ⟨g, hg, rfl⟩ hg0
  rw [leadingCoeff_leadingTerm]
  exact hG g hg (by rintro rfl; simp at hg0)

/-- The leading terms of a Gröbner basis `G` of `I` whose nonzero members have unit leading
coefficients form a Gröbner basis of the ideal of leading terms of `I`. -/
theorem IsGroebnerBasis.image_leadingTerm (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis (m.leadingTerm '' G) (Ideal.span (m.leadingTerm '' I)) := by
  refine (isGroebnerBasis_iff_forall_exists_degree_le_degree
    (isUnit_leadingCoeff_of_mem_image_leadingTerm hG)).2 ⟨?_, fun p hp hp0 ↦ ?_⟩
  · rw [h.span_leadingTerm_image]
    exact Ideal.subset_span
  · rw [h.span_leadingTerm_image] at hp
    obtain ⟨g, hg, hg0, hgp⟩ :=
      exists_degree_le_of_mem_span_leadingTerm hp (m.degree_mem_support hp0)
    exact ⟨m.leadingTerm g, ⟨g, hg, rfl⟩, (m.leadingTerm_eq_zero_iff g).not.2 hg0,
      (m.degree_leadingTerm g).symm ▸ hgp⟩

end CommSemiring

section CommRing

variable [CommRing R] {m} {f f₁ f₂ r r₁ r₂ : MvPolynomial σ R} {B G : Set (MvPolynomial σ R)}
  {I : Ideal (MvPolynomial σ R)}

/-- A polynomial differs from its remainders by an element of the ideal spanned by the divisors. -/
theorem IsRemainder.sub_mem_span (h : m.IsRemainder f B r) : f - r ∈ Ideal.span B := by
  obtain ⟨g, hf, -⟩ := h.exists_linearCombination
  rw [hf, add_sub_cancel_right, Finsupp.linearCombination_apply]
  exact Submodule.sum_mem _ fun b _ ↦ Submodule.smul_mem _ _ (Ideal.subset_span b.2)

/-- **Existence of remainders.** If every nonzero element of `B` has a unit leading coefficient,
then every polynomial has a remainder on division by `B`. -/
theorem exists_isRemainder (hB : ∀ b ∈ B, b ≠ 0 → IsUnit (m.leadingCoeff b))
    (f : MvPolynomial σ R) : ∃ r, m.IsRemainder f B r := by
  classical
  rcases eq_or_ne f 0 with rfl | hf
  · exact ⟨0, isRemainder_zero_left_iff.2 rfl⟩
  -- Divide by the nonzero elements of `B`, then extend the quotients by `0` to all of `B`.
  obtain ⟨g, r, hfgr, hdeg, hr⟩ := m.div_set (B := B \ {0}) (fun b hb ↦ hB b hb.1 hb.2) f
  refine ⟨r, ⟨g.mapDomain (Set.inclusion Set.sdiff_subset), ?_, fun b ↦ ?_⟩,
    fun c hc b hb hb0 ↦ hr c hc b ⟨hb, hb0⟩⟩
  · rwa [Finsupp.linearCombination_mapDomain]
  by_cases hb0 : (b : MvPolynomial σ R) = 0
  · simp [hb0]
  have hgb : g.mapDomain (Set.inclusion Set.sdiff_subset) b = g ⟨b, b.2, hb0⟩ :=
    Finsupp.mapDomain_apply_of_injective (Set.inclusion_injective _) g ⟨b, b.2, hb0⟩
  rw [hgb, ← map_add, ← withBotDegree_mul_of_left_mem_nonZeroDivisors
    (hB b b.2 hb0).mem_nonZeroDivisors, withBotDegree_le_withBotDegree_iff]
  exact ⟨hdeg ⟨b, b.2, hb0⟩, fun h ↦ absurd h hf⟩

/-- **Remainders modulo a Gröbner basis.** If `r₁` and `r₂` are remainders of `f₁` and `f₂` on
division by a Gröbner basis of `I`, then `f₁ - f₂ ∈ I` if and only if `r₁ = r₂`. -/
theorem IsGroebnerBasis.sub_mem_iff (h : m.IsGroebnerBasis G I) (h₁ : m.IsRemainder f₁ G r₁)
    (h₂ : m.IsRemainder f₂ G r₂) : f₁ - f₂ ∈ I ↔ r₁ = r₂ := by
  classical
  have hdiff : f₁ - f₂ - (r₁ - r₂) ∈ I := by
    have := Ideal.span_le.2 h.subset (Ideal.sub_mem _ h₁.sub_mem_span h₂.sub_mem_span)
    rwa [sub_sub_sub_comm] at this
  rw [← sub_add_cancel (f₁ - f₂) (r₁ - r₂), I.add_mem_iff_right hdiff]
  refine ⟨fun hr ↦ by_contra fun hne ↦ ?_, fun hr ↦ by simp [hr]⟩
  -- The leading monomial of the nonzero `r₁ - r₂ ∈ I` would be a reducible monomial of `r₁`
  -- or `r₂`.
  have hne' : r₁ - r₂ ≠ 0 := sub_ne_zero.2 hne
  obtain ⟨g, hgG, hg0, hgd⟩ := h.exists_degree_le_degree hr hne'
  rcases Finset.mem_union.1 (support_sub σ r₁ r₂ (m.degree_mem_support hne')) with hc | hc
  · exact h₁.not_degree_le hc hgG hg0 hgd
  · exact h₂.not_degree_le hc hgG hg0 hgd

/-- **Uniqueness of remainders.** Remainders on division by a Gröbner basis are unique. -/
theorem IsGroebnerBasis.eq_of_isRemainder (h : m.IsGroebnerBasis G I) (h₁ : m.IsRemainder f G r₁)
    (h₂ : m.IsRemainder f G r₂) : r₁ = r₂ :=
  (h.sub_mem_iff h₁ h₂).1 (by simp)

/-- **Ideal membership.** A remainder on division by a Gröbner basis of `I` vanishes if and only
if the divided polynomial lies in `I`. -/
theorem IsGroebnerBasis.remainder_eq_zero_iff_mem (h : m.IsGroebnerBasis G I)
    (hr : m.IsRemainder f G r) : r = 0 ↔ f ∈ I := by
  simpa using (h.sub_mem_iff hr (isRemainder_zero_left_iff.2 rfl)).symm

/-- If `r` is a remainder of `X^a` on division by a Gröbner basis of `I`, and `a` is the leading
exponent of a nonzero element of `I`, then `X^a - r` is a nonzero monic element of `I` with
leading exponent `a`. -/
theorem IsGroebnerBasis.monic_monomial_sub_of_isRemainder (h : m.IsGroebnerBasis G I)
    {a : σ →₀ ℕ} (hr : m.IsRemainder (monomial a 1) G r)
    {p : MvPolynomial σ R} (hp : p ∈ I) (hp0 : p ≠ 0) (hpa : m.degree p = a) :
    monomial a 1 - r ∈ I ∧ monomial a 1 - r ≠ 0 ∧ m.degree (monomial a 1 - r) = a ∧
      m.Monic (monomial a 1 - r) := by
  classical
  have hmem : monomial a 1 - r ∈ I := Ideal.span_le.2 h.subset hr.sub_mem_span
  have hcoeff : (monomial a 1 - r).coeff a = 1 := by
    have : a ∉ r.support := fun hc ↦ h.not_degree_le_of_isRemainder hr hc hp hp0 hpa.le
    simp [notMem_support_iff.1 this]
  have hne : monomial a 1 - r ≠ 0 := by
    have : Nontrivial R := nontrivial_of_ne _ _ (m.leadingCoeff_ne_zero_iff.2 hp0)
    exact fun h0 ↦ by simp [h0] at hcoeff
  -- The leading monomial is not a monomial of `r`, so it is `a`.
  have hdeg : m.degree (monomial a 1 - r) = a := by
    rcases Finset.mem_union.1 (support_sub σ _ _ (m.degree_mem_support hne)) with hc | hc
    · exact Finset.mem_singleton.1 (support_monomial_subset hc)
    · exact absurd le_rfl (h.not_degree_le_of_isRemainder hr hc hmem hne)
  exact ⟨hmem, hne, hdeg, by rw [Monic, leadingCoeff, hdeg, hcoeff]⟩

variable (m) in
/-- The polynomials `∑ g_b * b` over `b ∈ B` with `deg b + deg g_b ≤ d` for every `b`: the
`R`-span of the monomial multiples of elements of `B` of degree at most `d`. -/
private def boundedSpan (B : Set (MvPolynomial σ R)) (d : WithBot m.syn) :
    Submodule R (MvPolynomial σ R) where
  carrier := {p | ∃ g : B →₀ MvPolynomial σ R,
    p = Finsupp.linearCombination _ (fun b : B ↦ (b : MvPolynomial σ R)) g ∧
    ∀ b : B, m.toWithBotSyn (m.withBotDegree (b : MvPolynomial σ R)) +
      m.toWithBotSyn (m.withBotDegree (g b)) ≤ d}
  zero_mem' := ⟨0, by simp, by simp⟩
  add_mem' := by
    rintro _ _ ⟨g, rfl, hg⟩ ⟨g', rfl, hg'⟩
    refine ⟨g + g', by rw [map_add], fun b ↦ ?_⟩
    refine (add_le_add_right (m.withBotDegree_add_le _ _) _).trans ?_
    rw [← max_add_add_left]
    exact max_le (hg b) (hg' b)
  smul_mem' := by
    rintro r _ ⟨g, rfl, hg⟩
    refine ⟨r • g, by rw [LinearMap.map_smul_of_tower], fun b ↦ le_trans ?_ (hg b)⟩
    exact add_le_add_right (m.withBotDegree_le_withBotDegree_of_support_subset support_smul) _

/-- `boundedSpan m B d` is monotone in the bound `d`. -/
private theorem boundedSpan_mono {d d' : WithBot m.syn} (hdd' : d ≤ d') :
    boundedSpan m B d ≤ boundedSpan m B d' := by
  rintro _ ⟨g, rfl, hg⟩
  exact ⟨g, rfl, fun b ↦ (hg b).trans hdd'⟩

/-- An element of `boundedSpan m B d` lies in the ideal spanned by `B`. -/
private theorem mem_span_of_mem_boundedSpan {d : WithBot m.syn} {p : MvPolynomial σ R}
    (hp : p ∈ boundedSpan m B d) : p ∈ Ideal.span B := by
  obtain ⟨g, rfl, -⟩ := hp
  exact (Finsupp.mem_span_iff_linearCombination _ _ _).2 ⟨g, rfl⟩

/-- An element of `boundedSpan m B d` has degree at most `d`. -/
private theorem withBotDegree_le_of_mem_boundedSpan {d : WithBot m.syn} {p : MvPolynomial σ R}
    (hp : p ∈ boundedSpan m B d) : m.toWithBotSyn (m.withBotDegree p) ≤ d := by
  obtain ⟨g, rfl, hg⟩ := hp
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine m.withBotDegree_sum_le.trans (Finset.sup_le fun b _ ↦ ?_)
  exact (m.toWithBotSyn_withBotDegree_mul_le _ _).trans ((add_comm _ _).trans_le (hg b))

/-- An element of the ideal of `R` spanned by the leading coefficients of those `g ∈ G` with
`deg g ≤ D` is the coefficient of `X^D` in an element of `boundedSpan m G D`. -/
private theorem span_leadingCoeff_le_map_boundedSpan (D : σ →₀ ℕ) :
    Ideal.span (m.leadingCoeff '' {g ∈ G | m.degree g ≤ D}) ≤
      (boundedSpan m G (m.toSyn D)).map (lcoeff R D) := by
  classical
  rw [Ideal.span_le]
  rintro _ ⟨g, ⟨hgG, hgD⟩, rfl⟩
  -- `lc g` is the `D` coefficient of `X^(D - deg g) * g`.
  refine ⟨monomial (D - m.degree g) 1 * g,
    ⟨Finsupp.single ⟨g, hgG⟩ (monomial (D - m.degree g) 1), by simp, fun b ↦ ?_⟩, ?_⟩
  · rw [Finsupp.single_apply]
    split_ifs with h
    · subst h
      refine (add_le_add (m.toWithBotSyn_withBotDegree_le_toSyn_degree _)
        ((m.toWithBotSyn_withBotDegree_le_toSyn_degree _).trans
          (WithBot.coe_le_coe.2 (m.degree_monomial_le _)))).trans_eq ?_
      rw [← WithBot.coe_add, ← map_add, add_tsub_cancel_of_le hgD]
    · simp
  · simp [coeff_monomial_mul', tsub_tsub_cancel_of_le hgD, leadingCoeff]

/-- **Standard representations** (Adams–Loustaunau, Theorem 4.1.12): every element `f` of `I` is
`∑ g_b * b` over a Gröbner basis `G` of `I` with `deg b + deg g_b ≤ deg f` for every `b`.
No condition on leading coefficients is needed. -/
private theorem IsGroebnerBasis.mem_boundedSpan (h : m.IsGroebnerBasis G I) (hf : f ∈ I) :
    f ∈ boundedSpan m G (m.toWithBotSyn (m.withBotDegree f)) := by
  classical
  -- Induct on the degree of `f` in the well-founded synonym order.
  induction hd : m.toWithBotSyn (m.withBotDegree f) using WellFoundedLT.induction
    generalizing f with
  | ind d ih =>
  subst hd
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  have hW : m.toWithBotSyn (m.withBotDegree f) = m.toSyn (m.degree f) := by
    rw [(m.withBotDegree_eq_coe_degree_iff f).2 hf0, toWithBotSyn_apply_coe]
  -- Some `q ∈ boundedSpan m G (deg f)` has the same leading coefficient as `f`, and then
  -- `f - q ∈ I` has smaller degree than `f`.
  have hlt : m.leadingTerm f ∈ Ideal.span (m.leadingTerm '' G) :=
    h.span_leadingTerm_image ▸ Ideal.subset_span ⟨f, hf, rfl⟩
  have hc := coeff_mem_span_leadingCoeff hlt (m.degree f)
  rw [leadingTerm, coeff_monomial, ite_eq_left rfl] at hc
  obtain ⟨q, hq, hqf⟩ := span_leadingCoeff_le_map_boundedSpan (m.degree f) hc
  rw [← hW] at hq
  have hdeg := m.withBotDegree_sub_lt hf0 (withBotDegree_le_of_mem_boundedSpan hq) hqf
  have hqI : q ∈ I := Ideal.span_le.2 h.subset (mem_span_of_mem_boundedSpan hq)
  have := add_mem (boundedSpan_mono hdeg.le (ih _ hdeg (sub_mem hf hqI) rfl)) hq
  rwa [sub_add_cancel] at this

/-- For a Gröbner basis `G` of `I`, `0` is a remainder of `f` on division by `G` exactly when
`f ∈ I`. No condition on the leading coefficients of `G` is needed. -/
theorem IsGroebnerBasis.isRemainder_zero_iff_mem (h : m.IsGroebnerBasis G I) :
    m.IsRemainder f G 0 ↔ f ∈ I := by
  refine ⟨fun hr ↦ (h.remainder_eq_zero_iff_mem hr).1 rfl, fun hf ↦ ?_⟩
  obtain ⟨g, hg, hdeg⟩ := h.mem_boundedSpan hf
  exact ⟨⟨g, by rwa [add_zero], hdeg⟩, by simp⟩

/-- A Gröbner basis of `I` generates `I`. -/
theorem IsGroebnerBasis.ideal_eq_span (h : m.IsGroebnerBasis G I) : I = Ideal.span G := by
  refine le_antisymm (fun f hf ↦ ?_) (Ideal.span_le.2 h.subset)
  simpa using (h.isRemainder_zero_iff_mem.2 hf).sub_mem_span

/-- Remainders on division by a Gröbner basis whose nonzero members have unit leading
coefficients exist and are unique. -/
theorem IsGroebnerBasis.existsUnique_isRemainder (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) (f : MvPolynomial σ R) :
    ∃! r, m.IsRemainder f G r :=
  (exists_isRemainder hG f).elim fun r hr ↦ ⟨r, hr, fun _ hr' ↦ h.eq_of_isRemainder hr' hr⟩

/-- A subset `G` of `I` is a Gröbner basis of `I` if and only if every element of `I` has remainder
`0` on division by `G`. -/
theorem isGroebnerBasis_iff_isRemainder_zero :
    m.IsGroebnerBasis G I ↔ G ⊆ I ∧ ∀ f ∈ I, m.IsRemainder f G 0 := by
  refine ⟨fun h ↦ ⟨h.subset, fun f ↦ h.isRemainder_zero_iff_mem.2⟩, fun ⟨hGI, h0⟩ ↦ .mk hGI ?_⟩
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_mono (Set.image_mono hGI))
  rintro _ ⟨f, hf, rfl⟩
  exact leadingTerm_mem_span_leadingTerm_of_isRemainder_zero (h0 f hf)

end CommRing

end MonomialOrder

end

section
/- Source body: TauCeti/RingTheory/MvPolynomial/Groebner/Buchberger.lean -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Buchberger's criterion

Let `m` be a monomial order on `σ →₀ ℕ` and let `G` be a set of multivariate polynomials whose
nonzero members have unit leading coefficients, for instance any set of polynomials over a field.
Buchberger's criterion says that `G` is a Gröbner basis of the ideal it generates if and only if
`0` is a remainder of every S-polynomial `m.sPolynomial g₁ g₂` with `g₁, g₂ ∈ G` on division by `G`.
This turns the infinitely many conditions in the definition of a Gröbner basis into finitely many
checks when `G` is finite, and is the key step in the correctness of Buchberger's algorithm.

## Main results

* `MonomialOrder.IsGroebnerBasis.isRemainder_sPolynomial_zero`: the S-polynomials of a Gröbner
  basis have remainder `0`.
* `MonomialOrder.isGroebnerBasis_span_of_isRemainder_sPolynomial_zero`: **Buchberger's criterion**,
  if every S-polynomial of `G` has remainder `0` on division by `G`, then `G` is a Gröbner basis of
  `Ideal.span G`.
* `MonomialOrder.isGroebnerBasis_span_iff_isRemainder_sPolynomial_zero` and
  `MonomialOrder.isGroebnerBasis_iff_span_eq_and_isRemainder_sPolynomial_zero`: the resulting
  characterizations of Gröbner bases.

## Implementation notes

A remainder `0` of `f` on division by `G` is a *standard representation* `f = ∑ q_b * b` with
every `q_b * b` of degree at most that of `f`. The proof works with the `R`-span of the products
`X^a * b`, `b ∈ G`, whose degree `a + deg b` lies below a bound `d`. Products of degree exactly
`d` with `b ≠ 0` differ, after normalizing their leading coefficients, by monomial multiples of
S-polynomials, and these have representations of degree `< d` by hypothesis. So a representation
of degree at most `d` of a polynomial whose coefficient at `d` vanishes can be replaced by one of
degree `< d`, and well-founded induction on `d` shows that every element of `Ideal.span G` has a
standard representation. Its leading monomial is then divisible by the leading monomial of an
element of `G`.

The theorems hold over any commutative ring, assuming only that the nonzero members of `G` have
unit leading coefficients; over a field this is `MonomialOrder.isUnit_leadingCoeff`.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 2, §6, Theorem 6
  (Buchberger's criterion) and Lemma 5 (cancellation of leading terms by S-polynomials).
-/


namespace MonomialOrder

open MvPolynomial

variable {σ R : Type*} {m : MonomialOrder σ} [CommRing R] {G : Set (MvPolynomial σ R)}
  {I : Ideal (MvPolynomial σ R)}

variable (m) in
/-- The `R`-span of the products `X^a * b` with `b ∈ G` whose degree `a + deg b`, read in `m.syn`,
lies in `s`. For `s = Set.Iic d` it consists of the polynomials having a representation
`∑ q_b * b` by `G` with `deg q_b + deg b ≤ d` for every `b`. -/
private noncomputable def degreeSpan (G : Set (MvPolynomial σ R)) (s : Set m.syn) :
    Submodule R (MvPolynomial σ R) :=
  Submodule.span R {p | ∃ b ∈ G, ∃ a, m.toSyn (a + m.degree b) ∈ s ∧ p = monomial a 1 * b}

private theorem monomial_one_mul_mem_degreeSpan {s : Set m.syn} {b : MvPolynomial σ R}
    (hb : b ∈ G) {a : σ →₀ ℕ} (has : m.toSyn (a + m.degree b) ∈ s) :
    monomial a 1 * b ∈ degreeSpan m G s :=
  Submodule.subset_span ⟨b, hb, a, has, rfl⟩

private theorem degreeSpan_mono {s t : Set m.syn} (hst : s ⊆ t) :
    degreeSpan m G s ≤ degreeSpan m G t :=
  Submodule.span_mono fun _ ⟨b, hb, a, has, hp⟩ ↦ ⟨b, hb, a, hst has, hp⟩

private theorem mem_degreeSpan_self {b : MvPolynomial σ R} (hb : b ∈ G) :
    b ∈ degreeSpan m G (Set.Iic (m.toSyn (m.degree b))) := by
  simpa using monomial_one_mul_mem_degreeSpan (s := Set.Iic _) hb (a := 0) (by simp)

private theorem monomial_mul_mem_degreeSpan {d : m.syn} {p : MvPolynomial σ R}
    (hp : p ∈ degreeSpan m G (Set.Iic d)) (c : σ →₀ ℕ) (r : R) :
    monomial c r * p ∈ degreeSpan m G (Set.Iic (m.toSyn c + d)) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨b, hb, a, had, rfl⟩ := hp
    have hcab : monomial c r * (monomial a 1 * b) = r • (monomial (c + a) 1 * b) := by
      simp only [smul_eq_C_mul, ← mul_assoc, C_mul_monomial, monomial_mul_monomial, mul_one]
    rw [hcab]
    refine Submodule.smul_mem _ _ (monomial_one_mul_mem_degreeSpan hb ?_)
    rw [Set.mem_Iic, add_assoc, map_add]
    gcongr
    exact had
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul r' x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

private theorem mul_mem_degreeSpan {d : m.syn} {p : MvPolynomial σ R}
    (hp : p ∈ degreeSpan m G (Set.Iic d)) (q : MvPolynomial σ R) :
    q * p ∈ degreeSpan m G (Set.Iic (m.toSyn (m.degree q) + d)) := by
  have hq : q * p = ∑ c ∈ q.support, monomial c (q.coeff c) * p := by
    rw [← Finset.sum_mul, ← q.as_sum]
  rw [hq]
  refine Submodule.sum_mem _ fun c hc ↦ degreeSpan_mono ?_ (monomial_mul_mem_degreeSpan hp c _)
  exact Set.Iic_subset_Iic.2 (by gcongr; exact m.le_degree hc)

/-- A polynomial with remainder `0` on division by `G` has a representation by `G` of degree at
most its own degree. -/
private theorem IsRemainder.mem_degreeSpan {f : MvPolynomial σ R} (h : m.IsRemainder f G 0) :
    f ∈ degreeSpan m G (Set.Iic (m.toSyn (m.degree f))) := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem _
  obtain ⟨g, hfg, hdeg⟩ := h.exists_linearCombination
  generalize hV : degreeSpan m G (Set.Iic (m.toSyn (m.degree f))) = V
  rw [hfg, add_zero, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun b _ ↦ ?_
  rcases eq_or_ne (g b) 0 with hg | hg
  · simp [hg]
  rcases eq_or_ne (b : MvPolynomial σ R) 0 with hb | hb
  · simp [hb]
  rw [smul_eq_mul, ← hV]
  refine degreeSpan_mono (Set.Iic_subset_Iic.2 ?_) (mul_mem_degreeSpan (mem_degreeSpan_self b.2) _)
  rw [add_comm]
  exact (toWithBotSyn_withBotDegree_add_le_iff hb hg hf).1 (hdeg b)

/-- Every element of `Ideal.span G` has a representation by `G` of some bounded degree. -/
private theorem exists_mem_degreeSpan_of_mem_span {f : MvPolynomial σ R}
    (hf : f ∈ Ideal.span G) : ∃ d, f ∈ degreeSpan m G (Set.Iic d) := by
  induction hf using Submodule.span_induction with
  | mem b hb => exact ⟨_, mem_degreeSpan_self hb⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hx⟩ := hx
    obtain ⟨d₂, hy⟩ := hy
    exact ⟨d₁ ⊔ d₂, add_mem (degreeSpan_mono (Set.Iic_subset_Iic.2 le_sup_left) hx)
      (degreeSpan_mono (Set.Iic_subset_Iic.2 le_sup_right) hy)⟩
  | smul q x _ hx =>
    obtain ⟨d, hx⟩ := hx
    exact ⟨_, mul_mem_degreeSpan hx q⟩

/-- An element of the span of the products of degree `< d` lies in the span of the products of
degree at most some `d' < d`. -/
private theorem eq_zero_or_exists_mem_degreeSpan_Iic {d : m.syn} {f : MvPolynomial σ R}
    (hf : f ∈ degreeSpan m G (Set.Iio d)) :
    f = 0 ∨ ∃ d' < d, f ∈ degreeSpan m G (Set.Iic d') := by
  induction hf using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨b, hb, a, had, rfl⟩ := hp
    exact .inr ⟨_, had, monomial_one_mul_mem_degreeSpan hb le_rfl⟩
  | zero => exact .inl rfl
  | add x y _ _ hx hy =>
    rcases hx with rfl | ⟨d₁, hd₁, hx⟩
    · rwa [zero_add]
    rcases hy with rfl | ⟨d₂, hd₂, hy⟩
    · rw [add_zero]
      exact .inr ⟨d₁, hd₁, hx⟩
    exact .inr ⟨d₁ ⊔ d₂, max_lt hd₁ hd₂, add_mem
      (degreeSpan_mono (Set.Iic_subset_Iic.2 le_sup_left) hx)
      (degreeSpan_mono (Set.Iic_subset_Iic.2 le_sup_right) hy)⟩
  | smul r x _ hx =>
    rcases hx with rfl | ⟨d', hd', hx⟩
    · exact .inl (smul_zero r)
    exact .inr ⟨d', hd', Submodule.smul_mem _ r hx⟩

/-- If an element of the span of the products whose degrees lie in `s` has a nonzero coefficient
at `e`, then one of these products, with `b ≠ 0`, has degree at least `e`. -/
private theorem exists_le_of_mem_degreeSpan {s : Set m.syn} {f : MvPolynomial σ R}
    (hf : f ∈ degreeSpan m G s) {e : σ →₀ ℕ} (he : f.coeff e ≠ 0) :
    ∃ b ∈ G, b ≠ 0 ∧ ∃ a, m.toSyn (a + m.degree b) ∈ s ∧ m.toSyn e ≤ m.toSyn (a + m.degree b) := by
  by_contra! H
  have hle : degreeSpan m G s ≤ LinearMap.ker (lcoeff R e) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, a, has, rfl⟩
    rcases eq_or_ne b 0 with rfl | hb0
    · simp
    simpa using m.coeff_eq_zero_of_lt
      ((m.toSyn_degree_monomial_mul_le a 1 b).trans_lt (H b hb hb0 a has))
  exact he (by simpa using hle hf)

/-- **The reduction step.** If every S-polynomial of `G` has remainder `0` on division by `G`, a
representation of degree at most `D` of a polynomial whose coefficient at `D` vanishes can be
replaced by a representation of degree `< D`. -/
private theorem mem_degreeSpan_Iio_of_coeff_eq_zero
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (hS : ∀ g₁ ∈ G, ∀ g₂ ∈ G, m.IsRemainder (m.sPolynomial g₁ g₂) G 0) {D : σ →₀ ℕ}
    {f : MvPolynomial σ R} (hf : f ∈ degreeSpan m G (Set.Iic (m.toSyn D))) (hfD : f.coeff D = 0) :
    f ∈ degreeSpan m G (Set.Iio (m.toSyn D)) := by
  by_cases htop : ∃ b₀ ∈ G, b₀ ≠ 0 ∧ m.degree b₀ ≤ D
  swap
  · -- No product of degree exactly `D` is nonzero, so every product has degree `< D`.
    simp only [not_exists, not_and] at htop
    refine Submodule.span_le.2 ?_ hf
    rintro _ ⟨b, hb, a, had, rfl⟩
    rcases eq_or_ne b 0 with rfl | hb0
    · simp
    refine monomial_one_mul_mem_degreeSpan hb (lt_of_le_of_ne had fun h ↦ ?_)
    exact htop b hb hb0 (m.toSyn.injective h ▸ le_add_self)
  -- Fix a normalized product `q₀` of degree `D`. Every product `p` of degree at most `D` satisfies
  -- `p - p.coeff D • q₀ ∈ degreeSpan m G (Set.Iio D)`, and this condition is linear in `p`.
  obtain ⟨b₀, hb₀, hb₀0, hb₀D⟩ := htop
  obtain ⟨u₀, hu₀⟩ := hG b₀ hb₀ hb₀0
  set q₀ := monomial (D - m.degree b₀) (↑u₀⁻¹ : R) * b₀
  have hle : degreeSpan m G (Set.Iic (m.toSyn D)) ≤ (degreeSpan m G (Set.Iio (m.toSyn D))).comap
      (LinearMap.id - (lcoeff R D).smulRight q₀) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, a, had, rfl⟩
    rcases eq_or_ne b 0 with rfl | hb0
    · simp
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply, lcoeff_apply]
    rcases eq_or_ne (a + m.degree b) D with rfl | hne
    · -- The difference is a monomial multiple of `S(b, b₀)`, which has a representation of
      -- degree `deg S(b, b₀) < deg b ⊔ deg b₀`.
      rw [coeff_monomial_mul, one_mul, ← leadingCoeff,
        m.monomial_one_mul_sub_smul_eq_monomial_mul_sPolynomial hb₀D u₀ hu₀]
      set L := m.degree b ⊔ m.degree b₀
      rcases eq_or_ne (m.sPolynomial b b₀) 0 with hS0 | hS0
      · simp [hS0]
      refine degreeSpan_mono (Set.Iic_subset_Iio.2 ?_)
        (monomial_mul_mem_degreeSpan (hS b hb b₀ hb₀).mem_degreeSpan _ _)
      calc m.toSyn (a + m.degree b - L) + m.toSyn (m.degree (m.sPolynomial b b₀))
          < m.toSyn (a + m.degree b - L) + m.toSyn L := by
            gcongr; exact m.degree_sPolynomial_lt_sup_degree hS0
        _ = m.toSyn (a + m.degree b) := by
            rw [← map_add, tsub_add_cancel_of_le (sup_le le_add_self hb₀D)]
    · -- The product has degree `< D`, so its coefficient at `D` vanishes.
      have hlt : m.toSyn (a + m.degree b) < m.toSyn D :=
        lt_of_le_of_ne had (m.toSyn.injective.ne hne)
      rw [m.coeff_eq_zero_of_lt ((m.toSyn_degree_monomial_mul_le a 1 b).trans_lt hlt), zero_smul,
        sub_zero]
      exact monomial_one_mul_mem_degreeSpan hb hlt
  simpa [hfD] using hle hf

/-- If every S-polynomial of `G` has remainder `0` on division by `G`, then every polynomial with a
representation by `G` of degree at most `d` has a representation of degree at most its own
degree, so its leading monomial is divisible by the leading monomial of a nonzero element of
`G`. -/
private theorem exists_degree_le_degree_of_mem_degreeSpan
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (hS : ∀ g₁ ∈ G, ∀ g₂ ∈ G, m.IsRemainder (m.sPolynomial g₁ g₂) G 0) (d : m.syn)
    {f : MvPolynomial σ R} (hf : f ∈ degreeSpan m G (Set.Iic d)) (hf0 : f ≠ 0) :
    ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ m.degree f := by
  induction d using WellFoundedLT.induction generalizing f with
  | ind d ih =>
  obtain ⟨b, hb, hb0, a, had, hfa⟩ :=
    exists_le_of_mem_degreeSpan hf (m.coeff_degree_ne_zero_iff.2 hf0)
  rcases eq_or_ne (m.toSyn (m.degree f)) d with hfd | hfd
  · -- A product of degree exactly `deg f` occurs, so `deg b ≤ deg f`.
    have : a + m.degree b = m.degree f := m.toSyn.injective (le_antisymm (hfd ▸ had) hfa)
    exact ⟨b, hb, hb0, this ▸ le_add_self⟩
  · -- Otherwise `deg f < d`, and the representation can be improved.
    have hlt : m.toSyn (m.degree f) < d := lt_of_le_of_ne (hfa.trans had) hfd
    obtain ⟨D, rfl⟩ := m.toSyn.surjective d
    have hfD := mem_degreeSpan_Iio_of_coeff_eq_zero hG hS hf (m.coeff_eq_zero_of_lt hlt)
    obtain hf' | ⟨d', hd', hf'⟩ := eq_zero_or_exists_mem_degreeSpan_Iic hfD
    · exact absurd hf' hf0
    exact ih d' hd' hf' hf0

/-- The S-polynomials of two members of a Gröbner basis have remainder `0` on division by that
basis. -/
theorem IsGroebnerBasis.isRemainder_sPolynomial_zero (h : m.IsGroebnerBasis G I)
    {g₁ g₂ : MvPolynomial σ R} (hg₁ : g₁ ∈ G) (hg₂ : g₂ ∈ G) :
    m.IsRemainder (m.sPolynomial g₁ g₂) G 0 :=
  h.isRemainder_zero_iff_mem.2 (sPolynomial_mem_ideal (h.subset hg₁) (h.subset hg₂))

/-- **Buchberger's criterion.** If the nonzero members of `G` have unit leading coefficients and
the S-polynomial of any two members of `G` has remainder `0` on division by `G`, then `G` is a
Gröbner basis of the ideal it generates. -/
theorem isGroebnerBasis_span_of_isRemainder_sPolynomial_zero
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (hS : ∀ g₁ ∈ G, ∀ g₂ ∈ G, m.IsRemainder (m.sPolynomial g₁ g₂) G 0) :
    m.IsGroebnerBasis G (Ideal.span G) := by
  refine (isGroebnerBasis_iff_forall_exists_degree_le_degree hG).2
    ⟨Ideal.subset_span, fun f hf hf0 ↦ ?_⟩
  obtain ⟨d, hfd⟩ := exists_mem_degreeSpan_of_mem_span (m := m) hf
  exact exists_degree_le_degree_of_mem_degreeSpan hG hS d hfd hf0

/-- **Buchberger's criterion.** A set `G` whose nonzero members have unit leading coefficients is a
Gröbner basis of `I` if and only if it generates `I` and the S-polynomial of any two members of `G`
has remainder `0` on division by `G`. -/
theorem isGroebnerBasis_iff_span_eq_and_isRemainder_sPolynomial_zero
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis G I ↔
      Ideal.span G = I ∧ ∀ g₁ ∈ G, ∀ g₂ ∈ G, m.IsRemainder (m.sPolynomial g₁ g₂) G 0 := by
  refine ⟨fun h ↦ ⟨h.ideal_eq_span.symm, fun _ hg₁ _ hg₂ ↦
    h.isRemainder_sPolynomial_zero hg₁ hg₂⟩, ?_⟩
  rintro ⟨rfl, hS⟩
  exact isGroebnerBasis_span_of_isRemainder_sPolynomial_zero hG hS

/-- **Buchberger's criterion.** A set `G` whose nonzero members have unit leading coefficients is a
Gröbner basis of the ideal it generates if and only if the S-polynomial of any two members of `G`
has remainder `0` on division by `G`. -/
theorem isGroebnerBasis_span_iff_isRemainder_sPolynomial_zero
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis G (Ideal.span G) ↔
      ∀ g₁ ∈ G, ∀ g₂ ∈ G, m.IsRemainder (m.sPolynomial g₁ g₂) G 0 := by
  simpa using isGroebnerBasis_iff_span_eq_and_isRemainder_sPolynomial_zero (I := Ideal.span G) hG

end MonomialOrder

end

section
/- Source body: TauCeti/RingTheory/MvPolynomial/RestrictSupport.lean -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# The monomial basis of polynomials with restricted support

Mathlib's `MvPolynomial.basisRestrictSupport R s` is the basis of `MvPolynomial.restrictSupport R s`
indexed by `s`. This file records its coordinates (the coefficients) and its basis vectors (the
monomials with coefficient `1`).
-/


namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R] {s : Set (σ →₀ ℕ)}

/-- The coordinates of a polynomial in `basisRestrictSupport` are its coefficients. -/
@[simp]
theorem basisRestrictSupport_repr_apply (p : restrictSupport R s) (c : s) :
    (basisRestrictSupport R s).repr p c = (p : MvPolynomial σ R).coeff c :=
  -- `basisRestrictSupport` is defined through `AddMonoidAlgebra.supportedEquivFinsupp`, which
  -- reads off coefficients.
  rfl

/-- The basis vectors of `basisRestrictSupport` are the monomials with coefficient `1`. -/
@[simp]
theorem basisRestrictSupport_apply_coe (c : s) :
    (basisRestrictSupport R s c : MvPolynomial σ R) = monomial (c : σ →₀ ℕ) 1 := by
  classical
  have hc : monomial (c : σ →₀ ℕ) (1 : R) ∈ restrictSupport R s := by simp
  suffices basisRestrictSupport R s c = ⟨_, hc⟩ from congrArg Subtype.val this
  refine (basisRestrictSupport R s).repr.injective (Finsupp.ext fun d ↦ ?_)
  simp [Finsupp.single_apply, coeff_monomial, Subtype.ext_iff]

end MvPolynomial

end

section
/- Source body: TauCeti/RingTheory/MvPolynomial/Groebner/NormalForm.lean -/
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

section
/- Source body: CriticalPairGroebner.lean -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
The degree-span induction is adapted from
TauCeti/RingTheory/MvPolynomial/Groebner/Buchberger.lean,
commit 5ce4390a0a9a3277d048f680244409f42e9faeda.
-/

set_option autoImplicit false

/-! # Buchberger's criterion with strict lcm bounds

For arbitrary coefficient change, the degree of an S-polynomial can drop.
The correct invariant is that its representation uses generator multiples
strictly below the lcm of the two leading monomials.  This file proves that
version directly by well-founded degree reduction; it does not assume that
remainder certificates retain their old degree after coefficient change.
-/


namespace MonomialOrder

open MvPolynomial

variable {σ R : Type*} {m : MonomialOrder σ} [CommRing R] {G : Set (MvPolynomial σ R)}
  {I : Ideal (MvPolynomial σ R)}

variable (m) in
/-- The `R`-span of the products `X^a * b` with `b ∈ G` whose degree `a + deg b`, read in `m.syn`,
lies in `s`. For `s = Set.Iic d` it consists of the polynomials having a representation
`∑ q_b * b` by `G` with `deg q_b + deg b ≤ d` for every `b`. -/
noncomputable def criticalDegreeSpan (G : Set (MvPolynomial σ R)) (s : Set m.syn) :
    Submodule R (MvPolynomial σ R) :=
  Submodule.span R {p | ∃ b ∈ G, ∃ a, m.toSyn (a + m.degree b) ∈ s ∧ p = monomial a 1 * b}

theorem monomial_one_mul_mem_criticalDegreeSpan {s : Set m.syn} {b : MvPolynomial σ R}
    (hb : b ∈ G) {a : σ →₀ ℕ} (has : m.toSyn (a + m.degree b) ∈ s) :
    monomial a 1 * b ∈ criticalDegreeSpan m G s :=
  Submodule.subset_span ⟨b, hb, a, has, rfl⟩

theorem criticalDegreeSpan_mono {s t : Set m.syn} (hst : s ⊆ t) :
    criticalDegreeSpan m G s ≤ criticalDegreeSpan m G t :=
  Submodule.span_mono fun _ ⟨b, hb, a, has, hp⟩ ↦ ⟨b, hb, a, hst has, hp⟩

theorem mem_criticalDegreeSpan_self {b : MvPolynomial σ R} (hb : b ∈ G) :
    b ∈ criticalDegreeSpan m G (Set.Iic (m.toSyn (m.degree b))) := by
  simpa using monomial_one_mul_mem_criticalDegreeSpan (s := Set.Iic _) hb (a := 0) (by simp)

theorem monomial_mul_mem_criticalDegreeSpan {d : m.syn} {p : MvPolynomial σ R}
    (hp : p ∈ criticalDegreeSpan m G (Set.Iic d)) (c : σ →₀ ℕ) (r : R) :
    monomial c r * p ∈ criticalDegreeSpan m G (Set.Iic (m.toSyn c + d)) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨b, hb, a, had, rfl⟩ := hp
    have hcab : monomial c r * (monomial a 1 * b) = r • (monomial (c + a) 1 * b) := by
      simp only [smul_eq_C_mul, ← mul_assoc, C_mul_monomial, monomial_mul_monomial, mul_one]
    rw [hcab]
    refine Submodule.smul_mem _ _ (monomial_one_mul_mem_criticalDegreeSpan hb ?_)
    rw [Set.mem_Iic, add_assoc, map_add]
    gcongr
    exact had
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul r' x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem monomial_mul_mem_criticalDegreeSpan_Iio {d : m.syn} {p : MvPolynomial σ R}
    (hp : p ∈ criticalDegreeSpan m G (Set.Iio d)) (c : σ →₀ ℕ) (r : R) :
    monomial c r * p ∈ criticalDegreeSpan m G (Set.Iio (m.toSyn c + d)) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨b, hb, a, had, rfl⟩ := hp
    have hcab : monomial c r * (monomial a 1 * b) = r • (monomial (c + a) 1 * b) := by
      simp only [smul_eq_C_mul, ← mul_assoc, C_mul_monomial, monomial_mul_monomial, mul_one]
    rw [hcab]
    refine Submodule.smul_mem _ _ (monomial_one_mul_mem_criticalDegreeSpan hb ?_)
    rw [Set.mem_Iio, add_assoc, map_add]
    gcongr
    exact had
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul r' x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem mul_mem_criticalDegreeSpan {d : m.syn} {p : MvPolynomial σ R}
    (hp : p ∈ criticalDegreeSpan m G (Set.Iic d)) (q : MvPolynomial σ R) :
    q * p ∈ criticalDegreeSpan m G (Set.Iic (m.toSyn (m.degree q) + d)) := by
  have hq : q * p = ∑ c ∈ q.support, monomial c (q.coeff c) * p := by
    rw [← Finset.sum_mul, ← q.as_sum]
  rw [hq]
  refine Submodule.sum_mem _ fun c hc ↦ criticalDegreeSpan_mono ?_ (monomial_mul_mem_criticalDegreeSpan hp c _)
  exact Set.Iic_subset_Iic.2 (by gcongr; exact m.le_degree hc)

/-- A polynomial with remainder `0` on division by `G` has a representation by `G` of degree at
most its own degree. -/
theorem IsRemainder.mem_criticalDegreeSpan {f : MvPolynomial σ R} (h : m.IsRemainder f G 0) :
    f ∈ criticalDegreeSpan m G (Set.Iic (m.toSyn (m.degree f))) := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem _
  obtain ⟨g, hfg, hdeg⟩ := h.exists_linearCombination
  generalize hV : criticalDegreeSpan m G (Set.Iic (m.toSyn (m.degree f))) = V
  rw [hfg, add_zero, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun b _ ↦ ?_
  rcases eq_or_ne (g b) 0 with hg | hg
  · simp [hg]
  rcases eq_or_ne (b : MvPolynomial σ R) 0 with hb | hb
  · simp [hb]
  rw [smul_eq_mul, ← hV]
  refine criticalDegreeSpan_mono (Set.Iic_subset_Iic.2 ?_) (mul_mem_criticalDegreeSpan (mem_criticalDegreeSpan_self b.2) _)
  rw [add_comm]
  exact (toWithBotSyn_withBotDegree_add_le_iff hb hg hf).1 (hdeg b)

/-- Every element of `Ideal.span G` has a representation by `G` of some bounded degree. -/
theorem exists_mem_criticalDegreeSpan_of_mem_span {f : MvPolynomial σ R}
    (hf : f ∈ Ideal.span G) : ∃ d, f ∈ criticalDegreeSpan m G (Set.Iic d) := by
  induction hf using Submodule.span_induction with
  | mem b hb => exact ⟨_, mem_criticalDegreeSpan_self hb⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hx⟩ := hx
    obtain ⟨d₂, hy⟩ := hy
    exact ⟨d₁ ⊔ d₂, add_mem (criticalDegreeSpan_mono (Set.Iic_subset_Iic.2 le_sup_left) hx)
      (criticalDegreeSpan_mono (Set.Iic_subset_Iic.2 le_sup_right) hy)⟩
  | smul q x _ hx =>
    obtain ⟨d, hx⟩ := hx
    exact ⟨_, mul_mem_criticalDegreeSpan hx q⟩

/-- An element of the span of the products of degree `< d` lies in the span of the products of
degree at most some `d' < d`. -/
theorem eq_zero_or_exists_mem_criticalDegreeSpan_Iic {d : m.syn} {f : MvPolynomial σ R}
    (hf : f ∈ criticalDegreeSpan m G (Set.Iio d)) :
    f = 0 ∨ ∃ d' < d, f ∈ criticalDegreeSpan m G (Set.Iic d') := by
  induction hf using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨b, hb, a, had, rfl⟩ := hp
    exact .inr ⟨_, had, monomial_one_mul_mem_criticalDegreeSpan hb le_rfl⟩
  | zero => exact .inl rfl
  | add x y _ _ hx hy =>
    rcases hx with rfl | ⟨d₁, hd₁, hx⟩
    · rwa [zero_add]
    rcases hy with rfl | ⟨d₂, hd₂, hy⟩
    · rw [add_zero]
      exact .inr ⟨d₁, hd₁, hx⟩
    exact .inr ⟨d₁ ⊔ d₂, max_lt hd₁ hd₂, add_mem
      (criticalDegreeSpan_mono (Set.Iic_subset_Iic.2 le_sup_left) hx)
      (criticalDegreeSpan_mono (Set.Iic_subset_Iic.2 le_sup_right) hy)⟩
  | smul r x _ hx =>
    rcases hx with rfl | ⟨d', hd', hx⟩
    · exact .inl (smul_zero r)
    exact .inr ⟨d', hd', Submodule.smul_mem _ r hx⟩

/-- If an element of the span of the products whose degrees lie in `s` has a nonzero coefficient
at `e`, then one of these products, with `b ≠ 0`, has degree at least `e`. -/
theorem exists_le_of_mem_criticalDegreeSpan {s : Set m.syn} {f : MvPolynomial σ R}
    (hf : f ∈ criticalDegreeSpan m G s) {e : σ →₀ ℕ} (he : f.coeff e ≠ 0) :
    ∃ b ∈ G, b ≠ 0 ∧ ∃ a, m.toSyn (a + m.degree b) ∈ s ∧ m.toSyn e ≤ m.toSyn (a + m.degree b) := by
  by_contra! H
  have hle : criticalDegreeSpan m G s ≤ LinearMap.ker (lcoeff R e) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, a, has, rfl⟩
    rcases eq_or_ne b 0 with rfl | hb0
    · simp
    simpa using m.coeff_eq_zero_of_lt
      ((m.toSyn_degree_monomial_mul_le a 1 b).trans_lt (H b hb hb0 a has))
  exact he (by simpa using hle hf)

/-- **The reduction step.** If every S-polynomial of `G` has remainder `0` on division by `G`, a
representation of degree at most `D` of a polynomial whose coefficient at `D` vanishes can be
replaced by a representation of degree `< D`. -/
theorem mem_criticalDegreeSpan_Iio_of_coeff_eq_zero
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (hS : ∀ g₁ ∈ G, ∀ g₂ ∈ G,
      m.sPolynomial g₁ g₂ ∈ criticalDegreeSpan m G
        (Set.Iio (m.toSyn (m.degree g₁ ⊔ m.degree g₂)))) {D : σ →₀ ℕ}
    {f : MvPolynomial σ R} (hf : f ∈ criticalDegreeSpan m G (Set.Iic (m.toSyn D))) (hfD : f.coeff D = 0) :
    f ∈ criticalDegreeSpan m G (Set.Iio (m.toSyn D)) := by
  by_cases htop : ∃ b₀ ∈ G, b₀ ≠ 0 ∧ m.degree b₀ ≤ D
  swap
  · -- No product of degree exactly `D` is nonzero, so every product has degree `< D`.
    simp only [not_exists, not_and] at htop
    refine Submodule.span_le.2 ?_ hf
    rintro _ ⟨b, hb, a, had, rfl⟩
    rcases eq_or_ne b 0 with rfl | hb0
    · simp
    refine monomial_one_mul_mem_criticalDegreeSpan hb (lt_of_le_of_ne had fun h ↦ ?_)
    exact htop b hb hb0 (m.toSyn.injective h ▸ le_add_self)
  -- Fix a normalized product `q₀` of degree `D`. Every product `p` of degree at most `D` satisfies
  -- `p - p.coeff D • q₀ ∈ criticalDegreeSpan m G (Set.Iio D)`, and this condition is linear in `p`.
  obtain ⟨b₀, hb₀, hb₀0, hb₀D⟩ := htop
  obtain ⟨u₀, hu₀⟩ := hG b₀ hb₀ hb₀0
  set q₀ := monomial (D - m.degree b₀) (↑u₀⁻¹ : R) * b₀
  have hle : criticalDegreeSpan m G (Set.Iic (m.toSyn D)) ≤ (criticalDegreeSpan m G (Set.Iio (m.toSyn D))).comap
      (LinearMap.id - (lcoeff R D).smulRight q₀) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, hb, a, had, rfl⟩
    rcases eq_or_ne b 0 with rfl | hb0
    · simp
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply, lcoeff_apply]
    rcases eq_or_ne (a + m.degree b) D with rfl | hne
    · -- The difference is a monomial multiple of `S(b, b₀)`, which has a representation of
      -- degree `deg S(b, b₀) < deg b ⊔ deg b₀`.
      rw [coeff_monomial_mul, one_mul, ← leadingCoeff,
        m.monomial_one_mul_sub_smul_eq_monomial_mul_sPolynomial hb₀D u₀ hu₀]
      set L := m.degree b ⊔ m.degree b₀
      have hmul := monomial_mul_mem_criticalDegreeSpan_Iio
        (hS b hb b₀ hb₀) (a + m.degree b - L) ((u₀⁻¹ : Rˣ) : R)
      have hbound : m.toSyn (a + m.degree b - L) + m.toSyn L =
          m.toSyn (a + m.degree b) := by
        rw [← map_add, tsub_add_cancel_of_le (sup_le le_add_self hb₀D)]
      simpa only [L, hbound] using hmul
    · -- The product has degree `< D`, so its coefficient at `D` vanishes.
      have hlt : m.toSyn (a + m.degree b) < m.toSyn D :=
        lt_of_le_of_ne had (m.toSyn.injective.ne hne)
      rw [m.coeff_eq_zero_of_lt ((m.toSyn_degree_monomial_mul_le a 1 b).trans_lt hlt), zero_smul,
        sub_zero]
      exact monomial_one_mul_mem_criticalDegreeSpan hb hlt
  simpa [hfD] using hle hf

/-- If every S-polynomial of `G` has remainder `0` on division by `G`, then every polynomial with a
representation by `G` of degree at most `d` has a representation of degree at most its own
degree, so its leading monomial is divisible by the leading monomial of a nonzero element of
`G`. -/
theorem exists_degree_le_degree_of_mem_criticalDegreeSpan
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (hS : ∀ g₁ ∈ G, ∀ g₂ ∈ G,
      m.sPolynomial g₁ g₂ ∈ criticalDegreeSpan m G
        (Set.Iio (m.toSyn (m.degree g₁ ⊔ m.degree g₂)))) (d : m.syn)
    {f : MvPolynomial σ R} (hf : f ∈ criticalDegreeSpan m G (Set.Iic d)) (hf0 : f ≠ 0) :
    ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ m.degree f := by
  induction d using WellFoundedLT.induction generalizing f with
  | ind d ih =>
  obtain ⟨b, hb, hb0, a, had, hfa⟩ :=
    exists_le_of_mem_criticalDegreeSpan hf (m.coeff_degree_ne_zero_iff.2 hf0)
  rcases eq_or_ne (m.toSyn (m.degree f)) d with hfd | hfd
  · -- A product of degree exactly `deg f` occurs, so `deg b ≤ deg f`.
    have : a + m.degree b = m.degree f := m.toSyn.injective (le_antisymm (hfd ▸ had) hfa)
    exact ⟨b, hb, hb0, this ▸ le_add_self⟩
  · -- Otherwise `deg f < d`, and the representation can be improved.
    have hlt : m.toSyn (m.degree f) < d := lt_of_le_of_ne (hfa.trans had) hfd
    obtain ⟨D, rfl⟩ := m.toSyn.surjective d
    have hfD := mem_criticalDegreeSpan_Iio_of_coeff_eq_zero hG hS hf (m.coeff_eq_zero_of_lt hlt)
    obtain hf' | ⟨d', hd', hf'⟩ := eq_zero_or_exists_mem_criticalDegreeSpan_Iic hfD
    · exact absurd hf' hf0
    exact ih d' hd' hf' hf0

/-- The strict-lcm form of Buchberger's criterion over any commutative ring. -/
theorem isGroebnerBasis_span_of_sPolynomial_mem_criticalDegreeSpan
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (hS : ∀ g₁ ∈ G, ∀ g₂ ∈ G,
      m.sPolynomial g₁ g₂ ∈ criticalDegreeSpan m G
        (Set.Iio (m.toSyn (m.degree g₁ ⊔ m.degree g₂)))) :
    m.IsGroebnerBasis G (Ideal.span G) := by
  refine (isGroebnerBasis_iff_forall_exists_degree_le_degree hG).2
    ⟨Ideal.subset_span, fun f hf hf0 ↦ ?_⟩
  obtain ⟨d, hfd⟩ := exists_mem_criticalDegreeSpan_of_mem_span (m := m) hf
  exact exists_degree_le_degree_of_mem_criticalDegreeSpan hG hS d hfd hf0

/-- An already proved Gröbner basis supplies the strict critical-pair bounds. -/
theorem IsGroebnerBasis.sPolynomial_mem_criticalDegreeSpan
    (h : m.IsGroebnerBasis G I) {g₁ g₂ : MvPolynomial σ R}
    (hg₁ : g₁ ∈ G) (hg₂ : g₂ ∈ G) :
    m.sPolynomial g₁ g₂ ∈ criticalDegreeSpan m G
      (Set.Iio (m.toSyn (m.degree g₁ ⊔ m.degree g₂))) := by
  by_cases hzero : m.sPolynomial g₁ g₂ = 0
  · simp [hzero]
  exact criticalDegreeSpan_mono
    (Set.Iic_subset_Iio.mpr (m.degree_sPolynomial_lt_sup_degree hzero))
    (h.isRemainder_sPolynomial_zero hg₁ hg₂).mem_criticalDegreeSpan

end MonomialOrder

end

section
/- Source body: UniversalCoefficientGroebner.lean -/

set_option autoImplicit false

/-! # Gröbner bases under arbitrary coefficient maps

Unit leading coefficients survive every nontrivial coefficient ring.
Strict-lcm critical-pair representations transport even if intermediate
coefficients vanish.  Applying the proved strict-lcm Buchberger criterion
therefore establishes universal base change, without an injectivity or
flatness assumption on the coefficient map.
-/


namespace MonomialOrder

open MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S] {m : MonomialOrder σ}
variable {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}

theorem map_mem_criticalDegreeSpan (φ : R →+* S)
    (hdegree : ∀ g ∈ G, g ≠ 0 → m.degree (MvPolynomial.map φ g) = m.degree g)
    {p : MvPolynomial σ R} {s : Set m.syn}
    (hp : p ∈ criticalDegreeSpan m G s) :
    MvPolynomial.map φ p ∈ criticalDegreeSpan m (MvPolynomial.map φ '' G) s := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨b, hb, a, has, rfl⟩ := hp
    by_cases hb0 : b = 0
    · simp [hb0]
    rw [map_mul, map_monomial, map_one]
    apply monomial_one_mul_mem_criticalDegreeSpan (Set.mem_image_of_mem _ hb)
    simpa only [hdegree b hb hb0] using has
  | zero => simp
  | add p q hp hq ihp ihq => rw [map_add]; exact add_mem ihp ihq
  | smul a p hp ih =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ (φ a) ih

theorem sPolynomial_map_of_leadingCoeff_ne_zero (φ : R →+* S)
    {f g : MvPolynomial σ R} (hf : φ (m.leadingCoeff f) ≠ 0)
    (hg : φ (m.leadingCoeff g) ≠ 0) :
    m.sPolynomial (MvPolynomial.map φ f) (MvPolynomial.map φ g) =
      MvPolynomial.map φ (m.sPolynomial f g) := by
  simp only [sPolynomial, map_sub, map_mul, map_monomial,
    m.degree_map_of_leadingCoeff_ne_zero φ hf,
    m.degree_map_of_leadingCoeff_ne_zero φ hg,
    m.leadingCoeff_map_of_leadingCoeff_ne_zero φ hf,
    m.leadingCoeff_map_of_leadingCoeff_ne_zero φ hg]

/-- Every unit-leading-coefficient Gröbner basis is universal under coefficient
change.  The target ring is allowed to have zero divisors or to be trivial. -/
theorem IsGroebnerBasis.map_of_unit_leading
    (h : m.IsGroebnerBasis G I) (φ : R →+* S)
    (hunit : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis (MvPolynomial.map φ '' G) (I.map (MvPolynomial.map φ)) := by
  classical
  rcases subsingleton_or_nontrivial S with hS | hS
  · letI := hS
    have hu : ∀ g ∈ MvPolynomial.map φ '' G,
        g ≠ 0 → IsUnit (m.leadingCoeff g) := by
      intro g hg hg0
      exact (hg0 (Subsingleton.elim _ _)).elim
    apply (isGroebnerBasis_iff_forall_exists_degree_le_degree hu).mpr
    refine ⟨?_, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      exact Ideal.mem_map_of_mem _ (h.subset hg)
    · intro f hf hf0
      exact (hf0 (Subsingleton.elim _ _)).elim
  · letI := hS
    have hnonzero : ∀ g ∈ G, g ≠ 0 → φ (m.leadingCoeff g) ≠ 0 := by
      intro g hg hg0
      exact ((hunit g hg hg0).map φ).ne_zero
    have hdegree : ∀ g ∈ G, g ≠ 0 →
        m.degree (MvPolynomial.map φ g) = m.degree g := by
      intro g hg hg0
      exact m.degree_map_of_leadingCoeff_ne_zero φ (hnonzero g hg hg0)
    rw [h.ideal_eq_span, Ideal.map_span]
    apply isGroebnerBasis_span_of_sPolynomial_mem_criticalDegreeSpan
    · rintro _ ⟨g, hg, rfl⟩ hg0
      have hg0' : g ≠ 0 := fun hz => hg0 (by simp [hz])
      rw [m.leadingCoeff_map_of_leadingCoeff_ne_zero φ (hnonzero g hg hg0')]
      exact (hunit g hg hg0').map φ
    · rintro _ ⟨g₁, hg₁, rfl⟩ _ ⟨g₂, hg₂, rfl⟩
      by_cases h₁ : g₁ = 0
      · simp [h₁]
      by_cases h₂ : g₂ = 0
      · simp [h₂]
      rw [sPolynomial_map_of_leadingCoeff_ne_zero φ
        (hnonzero g₁ hg₁ h₁) (hnonzero g₂ hg₂ h₂), hdegree g₁ hg₁ h₁,
        hdegree g₂ hg₂ h₂]
      exact map_mem_criticalDegreeSpan φ hdegree
        (h.sPolynomial_mem_criticalDegreeSpan hg₁ hg₂)

theorem IsGroebnerBasis.standardMonomials_map_of_unit_leading [Nontrivial S]
    (h : m.IsGroebnerBasis G I) (φ : R →+* S)
    (hunit : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    m.standardMonomials (I.map (MvPolynomial.map φ)) = m.standardMonomials I := by
  have hmap := h.map_of_unit_leading φ hunit
  ext e
  rw [hmap.mem_standardMonomials_iff, h.mem_standardMonomials_iff]
  constructor
  · intro he g hg hg0
    have hn : φ (m.leadingCoeff g) ≠ 0 := ((hunit g hg hg0).map φ).ne_zero
    have hmap0 : MvPolynomial.map φ g ≠ 0 := by
      apply m.leadingCoeff_ne_zero_iff.mp
      rwa [m.leadingCoeff_map_of_leadingCoeff_ne_zero φ hn]
    simpa only [m.degree_map_of_leadingCoeff_ne_zero φ hn] using
      he _ (Set.mem_image_of_mem _ hg) hmap0
  · rintro he _ ⟨g, hg, rfl⟩ hg0
    have hg0' : g ≠ 0 := fun hz => hg0 (by simp [hz])
    have hn : φ (m.leadingCoeff g) ≠ 0 := ((hunit g hg hg0').map φ).ne_zero
    simpa only [m.degree_map_of_leadingCoeff_ne_zero φ hn] using he g hg hg0'

end MonomialOrder

end

#print axioms MonomialOrder.isGroebnerBasis_span_of_sPolynomial_mem_criticalDegreeSpan
#print axioms MonomialOrder.IsGroebnerBasis.map_of_unit_leading
#print axioms MonomialOrder.IsGroebnerBasis.standardMonomials_map_of_unit_leading


/- SOURCE TauCeti/RingTheory/MvPolynomial/Groebner/Map.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Gröbner bases under an injective change of coefficients

Let `m` be a monomial order on `σ →₀ ℕ` and let `φ : R →+* S` be an injective ring homomorphism,
for instance a field extension `k → K`. The coefficient map `MvPolynomial.map φ` does not change
supports, so it preserves leading monomials and commutes with leading coefficients, leading
terms and S-polynomials. It therefore carries remainders to remainders, and, by Buchberger's
criterion, a Gröbner basis `G` of an ideal `I` to a Gröbner basis `map φ '' G` of the extended
ideal `I.map (map φ)`, provided the nonzero members of `G` have unit leading coefficients.

So extending the coefficients changes neither Gröbner bases nor ideals of leading terms: the ideal
of leading terms of the extended ideal is the extension of the ideal of leading terms of `I`, and
the extended ideal contracts back to `I`. Over a field this holds for every ideal, since every
ideal is a Gröbner basis of itself and every nonzero polynomial has a unit leading coefficient.

## Main results

* `MonomialOrder.IsRemainder.map`: if `r` is a remainder of `f` on division by `B`, then
  `map φ r` is a remainder of `map φ f` on division by `map φ '' B`.
* `MonomialOrder.IsGroebnerBasis.map`: the image of a Gröbner basis of `I` whose nonzero members
  have unit leading coefficients is a Gröbner basis of `I.map (map φ)`.
* `MonomialOrder.isGroebnerBasis_map_iff`: conversely, a subset `G ⊆ I` whose nonzero members have
  unit leading coefficients is a Gröbner basis of `I` as soon as its image is a Gröbner basis of
  `I.map (map φ)`.
* `MonomialOrder.IsGroebnerBasis.comap_map_eq`: an ideal with such a Gröbner basis is the
  contraction of its extension.
* `MonomialOrder.IsGroebnerBasis.span_leadingTerm_map` and, over a field,
  `MonomialOrder.span_leadingTerm_map`: the ideal of leading terms of the extension of `I` is the
  extension of the ideal of leading terms of `I`.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 2, §6, Theorem 6
  (Buchberger's criterion), which shows that a Gröbner basis computation only involves the field
  of definition of the generators.
-/

section

namespace MonomialOrder

open MvPolynomial

variable {σ R S : Type*} {m : MonomialOrder σ}

section CommSemiring

variable [CommSemiring R] [CommSemiring S] {φ : R →+* S} {f r : MvPolynomial σ R}
  {B : Set (MvPolynomial σ R)}

/-- An injective coefficient map carries a remainder of `f` on division by `B` to a remainder of
the image of `f` on division by the image of `B`. -/
theorem IsRemainder.map (hφ : Function.Injective φ) (h : m.IsRemainder f B r) :
    m.IsRemainder (MvPolynomial.map φ f) (MvPolynomial.map φ '' B) (MvPolynomial.map φ r) := by
  classical
  obtain ⟨g, hfg, hdeg⟩ := h.exists_linearCombination
  -- The quotient attached to `map φ b` is `map φ` of the quotient attached to `b`.
  let e : B → MvPolynomial.map φ '' B := fun b ↦ ⟨_, Set.mem_image_of_mem _ b.2⟩
  have he : Function.Injective e := fun b c hbc ↦
    Subtype.ext (map_injective φ hφ (congrArg Subtype.val hbc))
  let g' : B →₀ MvPolynomial σ S := g.mapRange (MvPolynomial.map φ) (map_zero _)
  refine isRemainder_iff.2 ⟨⟨g'.mapDomain e, ?_, ?_⟩, ?_⟩
  · rw [Finsupp.linearCombination_mapDomain, hfg, map_add, Finsupp.linearCombination_apply,
      Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp), map_finsuppSum]
    simp [e]
  · rintro ⟨_, b, hb, rfl⟩
    have hgb : g'.mapDomain e ⟨_, Set.mem_image_of_mem _ hb⟩ = MvPolynomial.map φ (g ⟨b, hb⟩) :=
      Finsupp.mapDomain_apply_of_injective he g' ⟨b, hb⟩
    simpa only [hgb, m.withBotDegree_map_of_injective hφ] using hdeg ⟨b, hb⟩
  · rintro c hc _ ⟨b, hb, rfl⟩ hb0
    rw [support_map_of_injective _ hφ] at hc
    rw [m.degree_map_of_injective hφ]
    exact h.not_degree_le hc hb fun h ↦ hb0 (by rw [h, map_zero])

end CommSemiring

section CommRing

variable [CommRing R] [CommRing S] {φ : R →+* S} {G : Set (MvPolynomial σ R)}
  {I : Ideal (MvPolynomial σ R)}

/-- **Extension of coefficients.** An injective coefficient map `φ` carries a Gröbner basis of `I`
whose nonzero members have unit leading coefficients to a Gröbner basis of the extended ideal
`I.map (map φ)`. -/
theorem IsGroebnerBasis.map (hφ : Function.Injective φ) (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis (MvPolynomial.map φ '' G) (I.map (MvPolynomial.map φ)) := by
  rw [h.ideal_eq_span, Ideal.map_span]
  refine isGroebnerBasis_span_of_isRemainder_sPolynomial_zero ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩ hg0
    rw [m.leadingCoeff_map_of_injective hφ]
    exact (hG g hg fun h ↦ hg0 (by rw [h, map_zero])).map φ
  rintro _ ⟨g₁, hg₁, rfl⟩ _ ⟨g₂, hg₂, rfl⟩
  have := (h.isRemainder_sPolynomial_zero hg₁ hg₂).map hφ
  rwa [map_zero, ← m.sPolynomial_map_of_injective hφ] at this

/-- Let `φ` be an injective coefficient map and let `G ⊆ I` have nonzero members with unit leading
coefficients. Then `G` is a Gröbner basis of `I` if and only if `map φ '' G` is a Gröbner basis of
the extended ideal `I.map (map φ)`. -/
theorem isGroebnerBasis_map_iff (hφ : Function.Injective φ)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) (hGI : G ⊆ I) :
    m.IsGroebnerBasis (map φ '' G) (I.map (map φ)) ↔ m.IsGroebnerBasis G I := by
  refine ⟨fun h ↦ (isGroebnerBasis_iff_forall_exists_degree_le_degree hG).2
    ⟨hGI, fun p hp hp0 ↦ ?_⟩, fun h ↦ h.map hφ hG⟩
  obtain ⟨_, ⟨g, hg, rfl⟩, hg0, hle⟩ := h.exists_degree_le_degree (Ideal.mem_map_of_mem _ hp)
    ((map_ne_zero_iff _ (map_injective φ hφ)).2 hp0)
  rw [m.degree_map_of_injective hφ, m.degree_map_of_injective hφ] at hle
  exact ⟨g, hg, fun h ↦ hg0 (by rw [h, map_zero]), hle⟩

/-- **Contraction of an extended ideal.** If `I` has a Gröbner basis whose nonzero members have
unit leading coefficients, then the extension of `I` along an injective coefficient map `φ`
contracts back to `I`: a polynomial over `R` lying in the ideal generated by `I` over `S` already
lies in `I`. -/
theorem IsGroebnerBasis.comap_map_eq (hφ : Function.Injective φ) (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    (I.map (MvPolynomial.map φ)).comap (MvPolynomial.map φ) = I := by
  refine le_antisymm (fun f hf ↦ ?_) Ideal.le_comap_map
  -- The image of a remainder of `f` is a remainder of `map φ f ∈ I.map (map φ)`, hence zero.
  obtain ⟨r, hr⟩ := exists_isRemainder hG f
  have hr0 := ((h.map hφ hG).remainder_eq_zero_iff_mem (hr.map hφ)).2 hf
  rw [map_eq_zero_iff _ (map_injective φ hφ)] at hr0
  exact (h.remainder_eq_zero_iff_mem hr).1 hr0

/-- **Leading terms of an extended ideal.** If `I` has a Gröbner basis whose nonzero members have
unit leading coefficients, then the ideal of leading terms of the extension of `I` along an
injective coefficient map `φ` is the extension of the ideal of leading terms of `I`. -/
theorem IsGroebnerBasis.span_leadingTerm_map (hφ : Function.Injective φ)
    (h : m.IsGroebnerBasis G I) (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    Ideal.span (m.leadingTerm '' (I.map (MvPolynomial.map φ) : Set (MvPolynomial σ S))) =
      (Ideal.span (m.leadingTerm '' I)).map (MvPolynomial.map φ) := by
  rw [(h.map hφ hG).span_leadingTerm_image, h.span_leadingTerm_image, Ideal.map_span,
    Set.image_image, Set.image_image]
  simp_rw [m.leadingTerm_map_of_injective hφ]

/-- **Leading terms under extension of a field of coefficients.** For a field `k` and a ring
homomorphism `φ : k →+* S` to a nontrivial ring, for instance a field extension, the ideal of
leading terms of the extension of an ideal `I` of `k[σ]` is the extension of the ideal of leading
terms of `I`. -/
theorem span_leadingTerm_map {k : Type*} [Field k] [Nontrivial S] (φ : k →+* S)
    (I : Ideal (MvPolynomial σ k)) :
    Ideal.span (m.leadingTerm '' (I.map (map φ) : Set (MvPolynomial σ S))) =
      (Ideal.span (m.leadingTerm '' I)).map (map φ) :=
  (isGroebnerBasis_self I).span_leadingTerm_map φ.injective fun _ _ ↦ m.isUnit_leadingCoeff.2

end CommRing

end MonomialOrder

end
end


/- SOURCE TauCeti/Data/Finsupp/Colex.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Colexicographic order on exponents of bounded degree

This file studies the colexicographic order `Colex (α →₀ ℕ)` through the largest index of the
support.

## Main declarations

* `Finsupp.max'_lt_or_of_toColex_lt`: a colexicographic comparison of nonzero exponents compares
  their largest support indices, then the exponents there, then the remainders after erasing them.
* `Finsupp.wellFoundedOn_setOf_degree_le_toColex_gt`: when `α` has no infinite ascending chains,
  there is no infinite strictly increasing colexicographic chain of exponents of bounded degree.
  The bound on the degree is necessary, since `single a 1, single a 2, …` is colexicographically
  increasing.
-/

section

namespace Finsupp

variable {α : Type*} [LinearOrder α]

/-- If `toColex y < toColex x` for nonzero `y`, compare the largest indices `mx`, `my` of the
supports: either `my < mx`, or they agree and then either `y my < x mx`, or these exponents
also agree and the comparison persists after erasing that index. -/
theorem max'_lt_or_of_toColex_lt {x y : α →₀ ℕ} (hx : x.support.Nonempty)
    (hy : y.support.Nonempty) (h : toColex y < toColex x) :
    y.support.max' hy < x.support.max' hx ∨ y.support.max' hy = x.support.max' hx ∧
      (y (y.support.max' hy) < x (x.support.max' hx) ∨
        y (y.support.max' hy) = x (x.support.max' hx) ∧
          toColex (y.erase (y.support.max' hy)) < toColex (x.erase (x.support.max' hx))) := by
  -- `Colex (α →₀ ℕ)` is a type synonym and Mathlib has no evaluation lemma for `toColex` on
  -- `Finsupp`, so `Colex.lt_iff` evaluates `toColex f` through the coercion of `α →₀ ℕ`, which
  -- is definitionally `f`. We restate its components, and the goals below, at `α →₀ ℕ`.
  obtain ⟨i, hi, hlt⟩ := Colex.lt_iff.1 h
  have hi : ∀ j, i < j → y j = x j := hi
  have hlt : y i < x i := hlt
  have hix : i ≤ x.support.max' hx := x.support.le_max' i (mem_support_iff.2 (by omega))
  rcases lt_trichotomy (y.support.max' hy) (x.support.max' hx) with hm | hm | hm
  · exact Or.inl hm
  · refine Or.inr ⟨hm, ?_⟩
    rw [hm]
    rcases hix.lt_or_eq with hix | hix
    · refine Or.inr ⟨hi _ hix, Colex.lt_iff.2 ⟨i, fun j hj ↦ ?_, ?_⟩⟩
      · change (y.erase _) j = (x.erase _) j
        by_cases hjm : j = x.support.max' hx
        · simp [hjm]
        · simp [erase_ne hjm, hi j hj]
      · change (y.erase _) i < (x.erase _) i
        simpa [erase_ne hix.ne] using hlt
    · exact Or.inl (hix ▸ hlt)
  · exfalso
    have hxm : x (y.support.max' hy) = 0 :=
      notMem_support_iff.1 fun h ↦ (x.support.le_max' _ h).not_gt hm
    exact mem_support_iff.1 (y.support.max'_mem hy) ((hi _ (hix.trans_lt hm)).trans hxm)

/-- When `α` has no infinite ascending chains, the colexicographic order on exponents of degree
at most `n` has no infinite ascending chains either. -/
theorem wellFoundedOn_setOf_degree_le_toColex_gt [WellFoundedGT α] (n : ℕ) :
    {a : α →₀ ℕ | a.degree ≤ n}.WellFoundedOn (fun a b ↦ toColex b < toColex a) := by
  induction n with
  | zero =>
    refine Set.Subsingleton.wellFoundedOn fun a ha b hb ↦ ?_
    simp only [Set.mem_ofPred_eq, nonpos_iff_eq_zero, degree_eq_zero_iff] at ha hb
    rw [ha, hb]
  | succ n ih =>
    rw [Set.wellFoundedOn_iff] at ih ⊢
    -- A nonzero exponent is recorded by its largest index `m`, the exponent at `m`, and the
    -- remaining exponent of smaller degree; colex ascents increase this triple lexicographically.
    let F : {x : α →₀ ℕ // x ≠ 0} → α × ℕ × (α →₀ ℕ) := fun x ↦
      (x.1.support.max' (support_nonempty_iff.2 x.2),
        x.1 (x.1.support.max' (support_nonempty_iff.2 x.2)),
        x.1.erase (x.1.support.max' (support_nonempty_iff.2 x.2)))
    have hbdd : WellFounded fun e e' : ℕ ↦ e' < e ∧ e ≤ n + 1 :=
      (wellFounded_lt.onFun (f := fun e : ℕ ↦ n + 1 - e)).mono fun e e' h ↦ by
        simp only [Function.onFun]; omega
    have hwf := InvImage.wf F ((wellFounded_gt (α := α)).prod_lex (hbdd.prod_lex ih))
    have hdeg (x : α →₀ ℕ) (m : α) (hm : m ∈ x.support) :
        (x.erase m).degree + 1 ≤ x.degree := by
      have h := congr_arg degree (single_add_erase m x)
      rw [map_add, degree_single] at h
      have := mem_support_iff.1 hm
      omega
    have hacc (y : {x : α →₀ ℕ // x ≠ 0}) :
        Acc (fun a b ↦ toColex b < toColex a ∧ a ∈ {a : α →₀ ℕ | a.degree ≤ n + 1} ∧
          b ∈ {a : α →₀ ℕ | a.degree ≤ n + 1}) y.1 := by
      induction y using hwf.induction with
      | _ y ihy =>
        refine ⟨_, fun x ⟨hxy, hx, hy⟩ ↦ ?_⟩
        have hx0 : x ≠ 0 := by rintro rfl; exact (bot_le.not_gt hxy : _)
        refine ihy ⟨x, hx0⟩ ?_
        simp only [Set.mem_ofPred_eq] at hx hy
        have hxm := x.support.max'_mem (support_nonempty_iff.2 hx0)
        have hym := y.1.support.max'_mem (support_nonempty_iff.2 y.2)
        rcases max'_lt_or_of_toColex_lt _ _ hxy with hm | ⟨hm, he | ⟨he, hr⟩⟩
        · exact Prod.Lex.left _ _ hm
        · simp only [InvImage, F, hm]
          refine Prod.Lex.right _ (Prod.Lex.left _ _ ⟨hm ▸ he, ?_⟩)
          exact (le_degree _ _).trans hx
        · have hdx := hdeg x _ hxm
          have hdy := hdeg y.1 _ hym
          rw [hm] at he hr hdy
          simp only [InvImage, F, hm, he]
          exact Prod.Lex.right _ (Prod.Lex.right _ ⟨hr, by simp only [Set.mem_ofPred_eq]; omega,
            by simp only [Set.mem_ofPred_eq]; omega⟩)
    refine ⟨fun y ↦ ⟨_, fun x ⟨hxy, hx, hy⟩ ↦ ?_⟩⟩
    have hx0 : x ≠ 0 := by rintro rfl; exact (bot_le.not_gt hxy : _)
    exact hacc ⟨x, hx0⟩

end Finsupp

end

end


/- SOURCE TauCeti/Data/Finsupp/MonomialOrder/DegRevLex.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Graded reverse lexicographic monomial ordering

This file constructs the graded reverse lexicographic order (grevlex) on `σ →₀ ℕ` as a
`MonomialOrder`, alongside Mathlib's `MonomialOrder.lex` and `MonomialOrder.degLex`.

Monomials are first compared by total degree. Two monomials of the same degree are compared
at the *largest* index of `σ` where their exponents differ: the larger monomial is the one with
the *smaller* exponent there. With the antitone variable convention of `MonomialOrder.degLex`,
the largest index is the smallest variable, so this is the usual textbook rule: for variables
`X 0 > X 1 > ⋯ > X n`, the larger of two monomials of equal degree is the one whose rightmost
nonzero entry of the exponent difference is negative. On `Fin 3`, for instance,
`X 0 * X 2 < X 1 ^ 2` for grevlex, whereas `X 1 ^ 2 < X 0 * X 2` for deglex.

Equal-degree comparison is the reverse of the colexicographic order `Colex (σ →₀ ℕ)`.
Well-foundedness therefore rests on `Finsupp.wellFoundedOn_setOf_degree_le_toColex_gt`: when
`σ` has no infinite ascending chains, there is no infinite strictly increasing colexicographic
chain of exponents of bounded degree. The bound on the degree is necessary, since
`X 0, X 0 ^ 2, X 0 ^ 3, …` is colexicographically increasing.

## Main declarations

* `TauCeti.DegRevLex`: a type synonym carrying the graded reverse lexicographic order.
* `TauCeti.DegRevLex.lt_iff`, `TauCeti.DegRevLex.le_iff`: the order in terms of the degree and
  `Colex (σ →₀ ℕ)`.
* `TauCeti.DegRevLex.lt_iff_exists`: the textbook description by the largest differing index.
* `TauCeti.MonomialOrder.degRevLex`: the graded reverse lexicographic `MonomialOrder σ`, for
  `σ` linearly ordered with `WellFoundedGT σ` (automatic when `σ` is finite).
* `TauCeti.MonomialOrder.degRevLex_single_le_iff`: variables are ordered antitonely,
  `X i ≤ X j ↔ j ≤ i`, as for `MonomialOrder.degLex`.

## References

* [Cox, Little and O'Shea, *Ideals, varieties, and algorithms*][coxlittleoshea1997], Chapter 2,
  §2, Definition 6 (graded reverse lex order).
* [Becker and Weispfenning, *Gröbner bases*][Becker-Weispfenning1993]

The type-synonym interface follows Mathlib's `DegLex` (`Mathlib/Data/Finsupp/MonomialOrder/DegLex`,
by Antoine Chambert-Loir).
-/

section

namespace TauCeti

/-- A type synonym to equip a type with its graded reverse lexicographic order. -/
def DegRevLex (α : Type*) := α

variable {α : Type*}

/-- `toDegRevLex` is the identity function to the `DegRevLex` of a type. -/
@[match_pattern] def toDegRevLex : α ≃ DegRevLex α := Equiv.refl _

theorem toDegRevLex_injective : Function.Injective (toDegRevLex (α := α)) := fun _ _ ↦ _root_.id

theorem toDegRevLex_inj {a b : α} : toDegRevLex a = toDegRevLex b ↔ a = b := Iff.rfl

/-- `ofDegRevLex` is the identity function from the `DegRevLex` of a type. -/
@[match_pattern] def ofDegRevLex : DegRevLex α ≃ α := Equiv.refl _

theorem ofDegRevLex_injective : Function.Injective (ofDegRevLex (α := α)) := fun _ _ ↦ _root_.id

theorem ofDegRevLex_inj {a b : DegRevLex α} : ofDegRevLex a = ofDegRevLex b ↔ a = b := Iff.rfl

@[simp] theorem ofDegRevLex_symm_eq : (@ofDegRevLex α).symm = toDegRevLex := rfl

@[simp] theorem toDegRevLex_symm_eq : (@toDegRevLex α).symm = ofDegRevLex := rfl

@[simp] theorem ofDegRevLex_toDegRevLex (a : α) : ofDegRevLex (toDegRevLex a) = a := rfl

@[simp] theorem toDegRevLex_ofDegRevLex (a : DegRevLex α) : toDegRevLex (ofDegRevLex a) = a := rfl

/-- A recursor for `DegRevLex`. Use as `induction x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def DegRevLex.rec {β : DegRevLex α → Sort*} (h : ∀ a, β (toDegRevLex a)) :
    ∀ a, β a := fun a ↦ h (ofDegRevLex a)

@[simp] lemma DegRevLex.forall_iff {p : DegRevLex α → Prop} :
    (∀ a, p a) ↔ ∀ a, p (toDegRevLex a) := Iff.rfl

@[simp] lemma DegRevLex.exists_iff {p : DegRevLex α → Prop} :
    (∃ a, p a) ↔ ∃ a, p (toDegRevLex a) := Iff.rfl

noncomputable instance [AddCommMonoid α] : AddCommMonoid (DegRevLex α) :=
  ofDegRevLex.addCommMonoid

theorem toDegRevLex_add [AddCommMonoid α] (a b : α) :
    toDegRevLex (a + b) = toDegRevLex a + toDegRevLex b := rfl

theorem ofDegRevLex_add [AddCommMonoid α] (a b : DegRevLex α) :
    ofDegRevLex (a + b) = ofDegRevLex a + ofDegRevLex b := rfl

end TauCeti

end

section

namespace TauCeti

namespace DegRevLex

open Finsupp

variable [LinearOrder α]

/-- The graded reverse lexicographic order on `α →₀ ℕ`: compare total degrees, then compare
monomials of equal degree by the reverse of the colexicographic order. -/
noncomputable instance : LinearOrder (DegRevLex (α →₀ ℕ)) :=
  LinearOrder.lift'
    (fun f ↦ toLex ((ofDegRevLex f).degree, OrderDual.toDual (toColex (ofDegRevLex f))))
    fun f g h ↦ by simpa using congr_arg (fun p ↦ ofColex (OrderDual.ofDual (ofLex p).2)) h

/-- The graded reverse lexicographic order compares degrees first, then reverses the
colexicographic order. -/
theorem lt_iff {a b : DegRevLex (α →₀ ℕ)} :
    a < b ↔ (ofDegRevLex a).degree < (ofDegRevLex b).degree ∨
      (ofDegRevLex a).degree = (ofDegRevLex b).degree ∧
        toColex (ofDegRevLex b) < toColex (ofDegRevLex a) :=
  Prod.Lex.toLex_lt_toLex

/-- The non-strict form of `TauCeti.DegRevLex.lt_iff`. -/
theorem le_iff {a b : DegRevLex (α →₀ ℕ)} :
    a ≤ b ↔ (ofDegRevLex a).degree < (ofDegRevLex b).degree ∨
      (ofDegRevLex a).degree = (ofDegRevLex b).degree ∧
        toColex (ofDegRevLex b) ≤ toColex (ofDegRevLex a) :=
  Prod.Lex.toLex_le_toLex

/-- The textbook description of the graded reverse lexicographic order: among monomials of equal
degree, `a < b` when `a` has the larger exponent at the largest index where they differ. -/
theorem lt_iff_exists {a b : DegRevLex (α →₀ ℕ)} :
    a < b ↔ (ofDegRevLex a).degree < (ofDegRevLex b).degree ∨
      (ofDegRevLex a).degree = (ofDegRevLex b).degree ∧
        ∃ i, (∀ j, i < j → ofDegRevLex a j = ofDegRevLex b j) ∧
          ofDegRevLex b i < ofDegRevLex a i := by
  rw [lt_iff, Colex.lt_iff]
  refine or_congr_right (and_congr_right fun _ ↦ exists_congr fun i ↦ and_congr_left fun _ ↦ ?_)
  exact forall_congr' fun j ↦ imp_congr_right fun _ ↦ eq_comm

instance : IsOrderedCancelAddMonoid (DegRevLex (α →₀ ℕ)) where
  le_of_add_le_add_left a b c h := by
    rw [le_iff] at h ⊢
    simpa only [ofDegRevLex_add, map_add, add_lt_add_iff_left, add_right_inj, toColex_add,
      add_le_add_iff_left] using h
  add_le_add_left a b h c := by
    rw [le_iff] at h ⊢
    simpa only [ofDegRevLex_add, map_add, add_lt_add_iff_right, add_left_inj, toColex_add,
      add_le_add_iff_right] using h

theorem single_strictAnti : StrictAnti (fun a : α ↦ toDegRevLex (single a 1)) := fun _ _ h ↦
  lt_iff.2 (Or.inr ⟨by simp, Colex.single_lt_iff.2 h⟩)

theorem single_antitone : Antitone (fun a : α ↦ toDegRevLex (single a 1)) :=
  single_strictAnti.antitone

@[simp]
theorem single_lt_iff {a b : α} :
    toDegRevLex (single b 1) < toDegRevLex (single a 1) ↔ a < b :=
  single_strictAnti.lt_iff_gt

@[simp]
theorem single_le_iff {a b : α} :
    toDegRevLex (single b 1) ≤ toDegRevLex (single a 1) ↔ a ≤ b :=
  single_strictAnti.le_iff_ge

theorem monotone_degree :
    Monotone (fun x : DegRevLex (α →₀ ℕ) ↦ (ofDegRevLex x).degree) := fun _ _ h ↦ by
  rcases le_iff.1 h with h | h
  exacts [h.le, h.1.le]

/-- The graded reverse lexicographic order is well-founded when the indices have no infinite
ascending chains, for instance when there are finitely many of them. -/
instance wellFoundedLT [WellFoundedGT α] : WellFoundedLT (DegRevLex (α →₀ ℕ)) := by
  have hfib (n : ℕ) : ((fun x : DegRevLex (α →₀ ℕ) ↦ (ofDegRevLex x).degree) ⁻¹' {n}).WellFoundedOn
      (Function.onFun (· < ·) fun x ↦ OrderDual.toDual (toColex (ofDegRevLex x))) := by
    refine Set.wellFoundedOn_image.1 (((wellFoundedOn_setOf_degree_le_toColex_gt n).subset ?_))
    rintro _ ⟨x, hx, rfl⟩
    exact le_of_eq hx
  exact (WellFounded.prod_lex_of_wellFoundedOn_fiber wellFounded_lt.onFun hfib).mono
    fun a b (h : a < b) ↦ Prod.lex_def.2 <| by
      simpa only [OrderDual.toDual_lt_toDual] using lt_iff.1 h

end DegRevLex

namespace MonomialOrder

open Finsupp DegRevLex

variable {σ : Type*} [LinearOrder σ] [WellFoundedGT σ]

/-- The graded reverse lexicographic order on `σ →₀ ℕ`, as a `MonomialOrder`. Variables are
ordered antitonely, `X i ≤ X j ↔ j ≤ i`, so on `Fin n` the variable `X 0` is the largest. -/
noncomputable def degRevLex : MonomialOrder σ where
  syn := DegRevLex (σ →₀ ℕ)
  toSyn := { toEquiv := toDegRevLex, map_add' := toDegRevLex_add }
  toSyn_monotone a b h := by
    simp only [AddEquiv.coe_mk, DegRevLex.le_iff, ofDegRevLex_toDegRevLex]
    obtain ⟨c, rfl⟩ := exists_add_of_le h
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · exact Or.inl (by simpa [map_add, Nat.pos_iff_ne_zero, degree_eq_zero_iff] using hc)

open scoped _root_.MonomialOrder

theorem degRevLex_le_iff {a b : σ →₀ ℕ} :
    a ≼[degRevLex] b ↔ toDegRevLex a ≤ toDegRevLex b :=
  Iff.rfl

theorem degRevLex_lt_iff {a b : σ →₀ ℕ} :
    a ≺[degRevLex] b ↔ toDegRevLex a < toDegRevLex b :=
  Iff.rfl

@[simp]
theorem degRevLex_single_le_iff {a b : σ} :
    single a 1 ≼[degRevLex] single b 1 ↔ b ≤ a := by
  rw [degRevLex_le_iff, DegRevLex.single_le_iff]

@[simp]
theorem degRevLex_single_lt_iff {a b : σ} :
    single a 1 ≺[degRevLex] single b 1 ↔ b < a := by
  rw [degRevLex_lt_iff, DegRevLex.single_lt_iff]

end MonomialOrder

section Examples

open Finsupp _root_.TauCeti.MonomialOrder DegRevLex
open scoped _root_.MonomialOrder

/-- For the graded reverse lexicographic ordering, `X 1 < X 0`. -/
example : single (1 : Fin 2) 1 ≺[degRevLex] single 0 1 := by
  rw [degRevLex_single_lt_iff]
  exact Fin.zero_lt_one

/-- For the graded reverse lexicographic ordering, `X 0 * X 2 < X 1 ^ 2`. -/
example : single (0 : Fin 3) 1 + single 2 1 ≺[degRevLex] single 1 2 := by
  rw [degRevLex_lt_iff, lt_iff_exists]
  refine Or.inr ⟨by simp, 2, fun j hj ↦ ?_, by simp⟩
  exact absurd hj (Fin.not_lt.2 (Fin.le_last j))

/-- For the graded lexicographic ordering the comparison is the opposite: `X 1 ^ 2 < X 0 * X 2`. -/
example : single (1 : Fin 3) 2 ≺[_root_.MonomialOrder.degLex] single 0 1 + single 2 1 := by
  rw [_root_.MonomialOrder.degLex_lt_iff, Finsupp.DegLex.lt_iff]
  refine Or.inr ⟨by simp, ⟨0, fun j hj ↦ absurd hj (Fin.not_lt_zero j), by simp⟩⟩

/-- For the graded reverse lexicographic ordering, `X 0 < X 1 ^ 2`. -/
example : single (0 : Fin 2) 1 ≺[degRevLex] single 1 2 := by
  simp [degRevLex_lt_iff, lt_iff]

end Examples

end TauCeti

end
end


/- SOURCE archive_Definitions.lean -/
section

set_option autoImplicit false

/-!
# Faithful objects for symmetric northwest determinantal ideals

The independent variables are exactly the upper-triangular entries of a generic symmetric
matrix. Their order is the paper's folded order `(max i j, min i j)`. No auxiliary algebraic
variables or hypotheses on a rank array are built into the definitions.
-/

noncomputable section

namespace FourPapers.Symmetric

/-- The independent entries of a generic symmetric `n × n` matrix, ordered by larger endpoint
and then by smaller endpoint. Indices are zero-based. -/
abbrev Entry (n : ℕ) := {p : Fin n ×ₗ Fin n // p.2 ≤ p.1}

/-- Fold a matrix position across the diagonal to its independent coordinate. -/
def fold {n : ℕ} (i j : Fin n) : Entry n :=
  ⟨toLex (max i j, min i j), min_le_max⟩

@[simp] theorem fold_comm {n : ℕ} (i j : Fin n) : fold i j = fold j i := by
  apply Subtype.ext
  simp [fold, max_comm, min_comm]

@[simp] theorem fold_self {n : ℕ} (i : Fin n) :
    fold i i = ⟨toLex (i, i), le_rfl⟩ := by simp [fold]

/-- Folding identifies exactly a position and its transpose. -/
theorem fold_eq_iff {n : ℕ} (i j a b : Fin n) :
    fold i j = fold a b ↔ (i = a ∧ j = b) ∨ (i = b ∧ j = a) := by
  constructor
  · intro h
    have hmax : max i j = max a b := congrArg (fun e : Entry n => e.val.1) h
    have hmin : min i j = min a b := congrArg (fun e : Entry n => e.val.2) h
    by_cases hij : i ≤ j
    · by_cases hab : a ≤ b
      · left
        exact ⟨by simpa [min_eq_left hij, min_eq_left hab] using hmin,
          by simpa [max_eq_right hij, max_eq_right hab] using hmax⟩
      · right
        exact ⟨by simpa [min_eq_left hij, min_eq_right (le_of_not_ge hab)] using hmin,
          by simpa [max_eq_right hij, max_eq_left (le_of_not_ge hab)] using hmax⟩
    · by_cases hab : a ≤ b
      · right
        exact ⟨by simpa [max_eq_left (le_of_not_ge hij), max_eq_right hab] using hmax,
          by simpa [min_eq_right (le_of_not_ge hij), min_eq_left hab] using hmin⟩
      · left
        exact ⟨by simpa [max_eq_left (le_of_not_ge hij), max_eq_left (le_of_not_ge hab)] using hmax,
          by simpa [min_eq_right (le_of_not_ge hij), min_eq_right (le_of_not_ge hab)] using hmin⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact fold_comm _ _

/-- The coefficient ring of the symmetric generic matrix. -/
abbrev CoordinateRing (n : ℕ) (K : Type*) [CommRing K] := MvPolynomial (Entry n) K

/-- Generic symmetric matrix over its coordinate ring. -/
def genericMatrix (n : ℕ) (K : Type*) [CommRing K] :
    Matrix (Fin n) (Fin n) (CoordinateRing n K) := fun i j => MvPolynomial.X (fold i j)

@[simp] theorem genericMatrix_apply (n : ℕ) (K : Type*) [CommRing K] (i j : Fin n) :
    genericMatrix n K i j = MvPolynomial.X (fold i j) := rfl

@[simp] theorem genericMatrix_transpose (n : ℕ) (K : Type*) [CommRing K] :
    (genericMatrix n K).transpose = genericMatrix n K := by
  ext i j
  simp [Matrix.transpose_apply]

/-- A minor with strictly increasing row and column index lists. -/
def minor {n : ℕ} (K : Type*) [CommRing K] {t : ℕ}
    (a b : Fin t ↪o Fin n) : CoordinateRing n K :=
  ((genericMatrix n K).submatrix a b).det

/-- The exponent vector of the folded antidiagonal, retaining repeated variables. -/
def antidiagonalExponent {n t : ℕ} (a b : Fin t ↪o Fin n) : Entry n →₀ ℕ :=
  ∑ p : Fin t, Finsupp.single (fold (a p) (b p.rev)) 1

/-- The folded antidiagonal monomial, with coefficient one. -/
def antidiagonal {n : ℕ} (K : Type*) [CommRing K] {t : ℕ}
    (a b : Fin t ↪o Fin n) : CoordinateRing n K :=
  MvPolynomial.monomial (antidiagonalExponent a b) 1

/-- `r i j` is the rank bound in the northwest `(i+1) × (j+1)` rectangle. -/
abbrev RankArray (n : ℕ) := Fin n → Fin n → ℕ

/-- The exact set of prescribed northwest minors, including redundant ones. -/
def northwestGenerators {n : ℕ} (K : Type*) [CommRing K] (r : RankArray n) :
    Set (CoordinateRing n K) :=
  {f | ∃ (i j : Fin n) (a b : Fin (r i j + 1) ↪o Fin n),
    (∀ p, a p ≤ i) ∧ (∀ p, b p ≤ j) ∧ f = minor K a b}

/-- The ideal `I(r)` generated by all prescribed northwest minors. -/
def northwestIdeal {n : ℕ} (K : Type*) [CommRing K] (r : RankArray n) :
    Ideal (CoordinateRing n K) := Ideal.span (northwestGenerators K r)

/-- The exact corresponding folded antidiagonal generators. -/
def northwestAntidiagonals {n : ℕ} (K : Type*) [CommRing K] (r : RankArray n) :
    Set (CoordinateRing n K) :=
  {f | ∃ (i j : Fin n) (a b : Fin (r i j + 1) ↪o Fin n),
    (∀ p, a p ≤ i) ∧ (∀ p, b p ≤ j) ∧ f = antidiagonal K a b}

/-- The proposed initial ideal `J(r)`. -/
def northwestAntidiagonalIdeal {n : ℕ} (K : Type*) [CommRing K] (r : RankArray n) :
    Ideal (CoordinateRing n K) := Ideal.span (northwestAntidiagonals K r)

/-- All minors of one fixed size of the full symmetric matrix. -/
def fullMinorGenerators (n : ℕ) (K : Type*) [CommRing K] (t : ℕ) :
    Set (CoordinateRing n K) := {f | ∃ a b : Fin t ↪o Fin n, f = minor K a b}

/-- The full symmetric determinantal ideal `P_(n,t)`. -/
def determinantalIdeal (n : ℕ) (K : Type*) [CommRing K] (t : ℕ) :
    Ideal (CoordinateRing n K) := Ideal.span (fullMinorGenerators n K t)

/-- The prescribed folded graded reverse lexicographic monomial order. -/
noncomputable def foldedOrder (n : ℕ) : MonomialOrder (Entry n) :=
  TauCeti.MonomialOrder.degRevLex

/-- The initial ideal for exactly the prescribed folded monomial order. -/
noncomputable def initialIdeal {n : ℕ} (K : Type*) [CommRing K]
    (I : Ideal (CoordinateRing n K)) : Ideal (CoordinateRing n K) :=
  Ideal.span ((foldedOrder n).leadingTerm '' (I : Set (CoordinateRing n K)))

end FourPapers.Symmetric
end
end


/- SOURCE archive_StrictMonge.lean -/
section

set_option autoImplicit false

/-!
# The strict assignment inequality

A strict Monge inequality forces the reversing assignment to be the unique maximizer.
This is the order-theoretic argument needed for folded antidiagonal leading terms; its
codomain may be any linearly ordered cancellative additive monoid, including a monomial
order on exponent vectors.
-/

set_option maxHeartbeats 80000

namespace FourPapers.Symmetric

open Finset

variable {M : Type*} [AddCommMonoid M] [LinearOrder M] [IsOrderedCancelAddMonoid M]

/-- A strict exchange inequality for a cost matrix. -/
def StrictAntiMonge {t : ℕ} (c : Fin t → Fin t → M) : Prop :=
  ∀ i j p q, i < j → p < q → c i p + c j q < c i q + c j p

/-- The score of a permutation assignment. -/
def assignmentScore {t : ℕ} (c : Fin t → Fin t → M) (σ : Equiv.Perm (Fin t)) : M :=
  ∑ i, c i (σ i)

private theorem sum_swap_two {t : ℕ} (f g : Fin t → M) (i j : Fin t) (hij : i ≠ j)
    (hrest : ∀ k, k ≠ i → k ≠ j → f k = g k)
    (hpair : f i + f j < g i + g j) : ∑ k, f k < ∑ k, g k := by
  classical
  have hi : i ∈ (univ : Finset (Fin t)) := mem_univ _
  have hj : j ∈ univ.erase i := by simp [hij.symm]
  rw [← sum_erase_add _ _ hi, ← sum_erase_add _ _ hj]
  rw [← sum_erase_add _ _ hi, ← sum_erase_add _ _ hj]
  have hr : ∑ k ∈ (univ.erase i).erase j, f k = ∑ k ∈ (univ.erase i).erase j, g k := by
    apply sum_congr rfl
    intro k hk
    exact hrest k (by simpa using (mem_erase.mp (mem_erase.mp hk).2).1)
      (by simpa using (mem_erase.mp hk).1)
  rw [hr]
  simpa only [add_assoc, add_comm, add_left_comm] using
    add_lt_add_left hpair (∑ k ∈ (univ.erase i).erase j, g k)

/-- Swapping an increasing pair of assigned columns strictly increases the score. -/
theorem assignmentScore_swap_lt {t : ℕ} {c : Fin t → Fin t → M}
    (h : StrictAntiMonge c) (σ : Equiv.Perm (Fin t)) {i j : Fin t}
    (hij : i < j) (hσ : σ i < σ j) :
    assignmentScore c σ < assignmentScore c ((Equiv.swap i j).trans σ) := by
  classical
  apply sum_swap_two _ _ i j hij.ne
  · intro k hki hkj
    simp [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]
  · simpa using h i j (σ i) (σ j) hij hσ

private theorem strictAnti_eq_rev {t : ℕ} (σ : Equiv.Perm (Fin t))
    (hσ : StrictAnti (σ : Fin t → Fin t)) : σ = Fin.revPerm := by
  have hmono : StrictMono (fun i : Fin t => (σ i).rev) := Fin.rev_strictAnti.comp hσ
  have hid : (fun i : Fin t => (σ i).rev) = id := hmono.eq_id
  apply Equiv.ext
  intro i
  have h := congrFun hid i
  simpa using congrArg Fin.rev h

/-- The reversing assignment maximizes every strict anti-Monge score. -/
theorem assignmentScore_le_reverse {t : ℕ} {c : Fin t → Fin t → M}
    (h : StrictAntiMonge c) (σ : Equiv.Perm (Fin t)) :
    assignmentScore c σ ≤ assignmentScore c Fin.revPerm := by
  classical
  obtain ⟨τ, -, hτ⟩ := Finset.exists_max_image univ (assignmentScore c) univ_nonempty
  have hanti : StrictAnti (τ : Fin t → Fin t) := by
    intro i j hij
    by_contra hn
    have hne : τ i ≠ τ j := fun heq => hij.ne (τ.injective heq)
    have ht : τ i < τ j := lt_of_le_of_ne (not_lt.mp hn) hne
    exact (not_lt_of_ge (hτ ((Equiv.swap i j).trans τ) (mem_univ _)))
      (assignmentScore_swap_lt h τ hij ht)
  have ht := strictAnti_eq_rev τ hanti
  simpa [ht] using hτ σ (mem_univ _)

/-- Every other assignment has strictly smaller score than reversal. -/
theorem assignmentScore_lt_reverse {t : ℕ} {c : Fin t → Fin t → M}
    (h : StrictAntiMonge c) (σ : Equiv.Perm (Fin t)) (hσ : σ ≠ Fin.revPerm) :
    assignmentScore c σ < assignmentScore c Fin.revPerm := by
  have hn : ¬ StrictAnti (σ : Fin t → Fin t) := fun ha => hσ (strictAnti_eq_rev σ ha)
  unfold StrictAnti at hn
  push Not at hn
  obtain ⟨i, j, hij, hn⟩ := hn
  have hne : σ i ≠ σ j := fun heq => hij.ne (σ.injective heq)
  have ht : σ i < σ j := lt_of_le_of_ne hn hne
  exact (assignmentScore_swap_lt h σ hij ht).trans_le
    (assignmentScore_le_reverse h ((Equiv.swap i j).trans σ))

end FourPapers.Symmetric
end


/- SOURCE archive_LeadingMinors.lean -/
section

set_option autoImplicit false

/-!
# Folded antidiagonal leading terms

The exchange comparison is proved after folding: the southeast corner has a strictly
larger folded index than both crossed corners. The strict assignment theorem then treats
all minor sizes and every permutation term, including repeated symmetric entries.
-/

noncomputable section

namespace FourPapers.Symmetric

open Finset Finsupp MvPolynomial
open scoped MonomialOrder

variable {n t : ℕ}

/-- Folding is strictly increasing separately in either endpoint. -/
theorem fold_strictMono_left (j : Fin n) : StrictMono (fun i : Fin n => fold i j) := by
  intro a c hac
  change toLex (max a j, min a j) < toLex (max c j, min c j)
  rw [Prod.Lex.toLex_lt_toLex]
  by_cases hcj : c ≤ j
  · exact Or.inr ⟨by simp [max_eq_right hcj, max_eq_right (hac.le.trans hcj)],
      by simpa [min_eq_left hcj, min_eq_left (hac.le.trans hcj)] using hac⟩
  · have hjc : j < c := lt_of_not_ge hcj
    by_cases haj : a ≤ j
    · exact Or.inl (by simpa [max_eq_right haj, max_eq_left hjc.le] using hjc)
    · exact Or.inl (by simpa [max_eq_left (le_of_not_ge haj), max_eq_left hjc.le] using hac)

/-- Symmetry gives strict monotonicity in the second endpoint as well. -/
theorem fold_strictMono_right (i : Fin n) : StrictMono (fold i) := by
  simpa only [fold_comm] using fold_strictMono_left i

/-- One crossing swap increases a determinant term under the folded antidiagonal order. -/
theorem crossed_pair_lt {a b c d : Fin n} (hac : a < c) (hbd : b < d) :
    (single (fold a b) 1 + single (fold c d) 1 : Entry n →₀ ℕ) ≺[foldedOrder n]
      single (fold a d) 1 + single (fold c b) 1 := by
  have hab : fold a b < fold c d :=
    (fold_strictMono_left b hac).trans (fold_strictMono_right c hbd)
  have had : fold a d < fold c d := fold_strictMono_left d hac
  have hcb : fold c b < fold c d := fold_strictMono_right c hbd
  change TauCeti.toDegRevLex (single (fold a b) 1 + single (fold c d) 1 : Entry n →₀ ℕ) <
    TauCeti.toDegRevLex (single (fold a d) 1 + single (fold c b) 1 : Entry n →₀ ℕ)
  rw [TauCeti.DegRevLex.lt_iff_exists]
  refine Or.inr ⟨by simp, fold c d, ?_, ?_⟩
  · intro k hk
    have h1 := (hab.trans hk).ne
    have h2 := hk.ne
    have h3 := (had.trans hk).ne
    have h4 := (hcb.trans hk).ne
    simp only [TauCeti.ofDegRevLex_toDegRevLex, Finsupp.add_apply, single_apply, h1, h1.symm, h2, h2.symm,
      h3, h3.symm, h4, h4.symm, ite_false, zero_add]
  · simp only [TauCeti.ofDegRevLex_toDegRevLex, Finsupp.add_apply, single_apply, hab.ne, had.ne, hcb.ne, ite_false, ite_true, zero_add, add_zero, Nat.zero_lt_one]

/-- Exponents of a permutation term in the Leibniz expansion of a minor. -/
def permutationExponent (a b : Fin t ↪o Fin n) (σ : Equiv.Perm (Fin t)) : Entry n →₀ ℕ :=
  ∑ p, single (fold (a (σ p)) (b p)) 1

/-- Reversing the rows has the antidiagonal exponent specified in the paper. -/
theorem permutationExponent_reverse (a b : Fin t ↪o Fin n) :
    permutationExponent a b Fin.revPerm = antidiagonalExponent a b := by
  classical
  unfold permutationExponent antidiagonalExponent
  simpa using Equiv.sum_comp Fin.revPerm
    (fun p : Fin t => single (fold (a p) (b p.rev)) 1)

/-- The assignment score is strict anti-Monge in the folded monomial order. -/
theorem folded_assignment_strictAntiMonge (a b : Fin t ↪o Fin n) :
    StrictAntiMonge (fun p q : Fin t =>
      (foldedOrder n).toSyn (single (fold (a q) (b p)) 1)) := by
  intro i j p q hij hpq
  simpa only [← map_add, add_comm] using crossed_pair_lt (a.strictMono hpq) (b.strictMono hij)

/-- Every other permutation term of every symmetric minor is strictly smaller than its
folded antidiagonal. In particular, symmetry cannot create cancellation of the leading term. -/
theorem permutationExponent_lt_antidiagonal (a b : Fin t ↪o Fin n)
    (σ : Equiv.Perm (Fin t)) (hσ : σ ≠ Fin.revPerm) :
    permutationExponent a b σ ≺[foldedOrder n] antidiagonalExponent a b := by
  have h := assignmentScore_lt_reverse (folded_assignment_strictAntiMonge a b) σ hσ
  simp only [assignmentScore, ← map_sum] at h
  change permutationExponent a b σ ≺[foldedOrder n]
    permutationExponent a b Fin.revPerm at h
  rwa [permutationExponent_reverse] at h

/-- Every permutation term is at most the antidiagonal. -/
theorem permutationExponent_le_antidiagonal (a b : Fin t ↪o Fin n)
    (σ : Equiv.Perm (Fin t)) :
    permutationExponent a b σ ≼[foldedOrder n] antidiagonalExponent a b := by
  by_cases hσ : σ = Fin.revPerm
  · subst σ
    rw [permutationExponent_reverse]
  · exact (permutationExponent_lt_antidiagonal a b σ hσ).le

/-- The product in one determinant term is exactly the corresponding monomial, with all
folded multiplicities retained. -/
theorem permutation_product (K : Type*) [CommRing K] (a b : Fin t ↪o Fin n)
    (σ : Equiv.Perm (Fin t)) :
    (∏ p, genericMatrix n K (a (σ p)) (b p)) =
      monomial (permutationExponent a b σ) 1 := by
  classical
  symm
  exact monomial_sum_one univ (fun p => single (fold (a (σ p)) (b p)) 1)

end FourPapers.Symmetric
end
end


/- SOURCE archive_MinorLeadingTerm.lean -/
section

set_option autoImplicit false

/-!
# The leading term of every symmetric minor

The coefficient computation is over an arbitrary commutative ring. In particular, no
characteristic assumption is used, and the repeated symmetric coordinates in a folded
antidiagonal are retained as genuine multiplicities.
-/

namespace FourPapers.Symmetric

open Finset Finsupp MvPolynomial
open scoped MonomialOrder

variable {n t : ℕ}

/-- The determinant sign as an element of the coefficient ring. -/
def signCoefficient (K : Type*) [CommRing K] (σ : Equiv.Perm (Fin t)) : K :=
  Equiv.Perm.sign σ • (1 : K)

theorem signCoefficient_eq_one_or_neg_one (K : Type*) [CommRing K]
    (σ : Equiv.Perm (Fin t)) :
    signCoefficient K σ = 1 ∨ signCoefficient K σ = -1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · left
    simp [signCoefficient, h]
  · right
    simp [signCoefficient, h, Units.smul_def]

theorem signCoefficient_mul_self (K : Type*) [CommRing K]
    (σ : Equiv.Perm (Fin t)) : signCoefficient K σ * signCoefficient K σ = 1 := by
  rcases signCoefficient_eq_one_or_neg_one K σ with h | h <;> simp [h]

theorem signCoefficient_isUnit (K : Type*) [CommRing K]
    (σ : Equiv.Perm (Fin t)) : IsUnit (signCoefficient K σ) := by
  rcases signCoefficient_eq_one_or_neg_one K σ with h | h <;> simp [h]

theorem signCoefficient_ne_zero (K : Type*) [CommRing K] [Nontrivial K]
    (σ : Equiv.Perm (Fin t)) : signCoefficient K σ ≠ 0 :=
  (signCoefficient_isUnit K σ).ne_zero

/-- The Leibniz expansion after folding the symmetric entries. -/
theorem minor_eq_sum (K : Type*) [CommRing K] (a b : Fin t ↪o Fin n) :
    minor K a b = ∑ σ : Equiv.Perm (Fin t),
      monomial (permutationExponent a b σ) (signCoefficient K σ) := by
  classical
  unfold minor
  rw [Matrix.det_apply]
  apply sum_congr rfl
  intro σ _
  simp only [Matrix.submatrix_apply, permutation_product, smul_monomial, signCoefficient]

/-- The folded antidiagonal appears exactly once in the determinant expansion. -/
theorem minor_coeff_antidiagonal (K : Type*) [CommRing K] (a b : Fin t ↪o Fin n) :
    (minor K a b).coeff (antidiagonalExponent a b) =
      signCoefficient K (Fin.revPerm : Equiv.Perm (Fin t)) := by
  classical
  rw [minor_eq_sum, coeff_sum]
  rw [Finset.sum_eq_single (Fin.revPerm : Equiv.Perm (Fin t))]
  · simp [permutationExponent_reverse]
  · intro σ _ hσ
    have hne : permutationExponent a b σ ≠ antidiagonalExponent a b := by
      intro heq
      exact (permutationExponent_lt_antidiagonal a b σ hσ).ne
        (congrArg (foldedOrder n).toSyn heq)
    simp [hne]
  · simp

/-- No exponent in the support of a minor exceeds its folded antidiagonal. -/
theorem minor_degree_le_antidiagonal (K : Type*) [CommRing K]
    (a b : Fin t ↪o Fin n) :
    (foldedOrder n).degree (minor K a b) ≼[foldedOrder n] antidiagonalExponent a b := by
  classical
  rw [minor_eq_sum]
  apply (foldedOrder n).degree_sum_le.trans
  apply Finset.sup_le
  intro σ _
  exact ((foldedOrder n).degree_monomial_le (signCoefficient K σ)).trans
    (permutationExponent_le_antidiagonal a b σ)

/-- Lemma 3.1: the degree of every minor is its folded antidiagonal exponent. -/
theorem minor_degree (K : Type*) [CommRing K] [Nontrivial K]
    (a b : Fin t ↪o Fin n) :
    (foldedOrder n).degree (minor K a b) = antidiagonalExponent a b := by
  apply (foldedOrder n).toSyn.injective
  apply le_antisymm (minor_degree_le_antidiagonal K a b)
  apply (foldedOrder n).le_degree
  rw [MvPolynomial.mem_support_iff, minor_coeff_antidiagonal]
  exact signCoefficient_ne_zero K _

/-- The leading coefficient is a determinant sign, in every coefficient ring. -/
theorem minor_leadingCoeff (K : Type*) [CommRing K]
    (a b : Fin t ↪o Fin n) :
    (foldedOrder n).leadingCoeff (minor K a b) =
      signCoefficient K (Fin.revPerm : Equiv.Perm (Fin t)) := by
  nontriviality K
  rw [MonomialOrder.leadingCoeff, minor_degree, minor_coeff_antidiagonal]

/-- The full leading term, including its coefficient. -/
theorem minor_leadingTerm (K : Type*) [CommRing K]
    (a b : Fin t ↪o Fin n) :
    (foldedOrder n).leadingTerm (minor K a b) =
      monomial (antidiagonalExponent a b)
        (signCoefficient K (Fin.revPerm : Equiv.Perm (Fin t))) := by
  nontriviality K
  rw [MonomialOrder.leadingTerm, minor_degree, minor_leadingCoeff]

/-- In particular every leading coefficient is a unit, even in characteristic two. -/
theorem minor_leadingCoeff_isUnit (K : Type*) [CommRing K]
    (a b : Fin t ↪o Fin n) :
    IsUnit ((foldedOrder n).leadingCoeff (minor K a b)) := by
  rw [minor_leadingCoeff]
  exact signCoefficient_isUnit K _

/-- All proposed northwest antidiagonals occur in the initial ideal. The reverse inclusion
is the substantive additional assertion of the paper's Gröbner basis theorem. -/
theorem northwestAntidiagonalIdeal_le_initial (K : Type*) [CommRing K]
    (r : RankArray n) :
    northwestAntidiagonalIdeal K r ≤ initialIdeal K (northwestIdeal K r) := by
  apply Ideal.span_le.mpr
  rintro f ⟨i, j, a, b, ha, hb, rfl⟩
  change antidiagonal K a b ∈ initialIdeal K (northwestIdeal K r)
  have hm : minor K a b ∈ northwestIdeal K r :=
    Ideal.subset_span ⟨i, j, a, b, ha, hb, rfl⟩
  have hlt : (foldedOrder n).leadingTerm (minor K a b) ∈
      initialIdeal K (northwestIdeal K r) :=
    Ideal.subset_span ⟨minor K a b, hm, rfl⟩
  have hmul := (initialIdeal K (northwestIdeal K r)).mul_mem_left
    (C (signCoefficient K (Fin.revPerm : Equiv.Perm (Fin (r i j + 1))))) hlt
  simpa only [minor_leadingTerm, C_mul_monomial, signCoefficient_mul_self,
    antidiagonal] using hmul

end FourPapers.Symmetric
end


/- SOURCE remote_SymbolicPower.lean -/
section

set_option autoImplicit false

/-!
# Symbolic powers with their localization meaning proved

The construction is defined for an arbitrary ideal so that the main determinantal theorem
need not assume its own primeness conclusion. For a prime ideal, we prove the defining
membership criterion and identify it with contraction from localization at that prime.
-/

noncomputable section

namespace FourPapers.Symmetric

variable {R : Type*} [CommRing R]

/-- The span of fractions-clearing witnesses for the `s`th symbolic power. For prime `P`,
the span introduces no additional elements; this is proved below. -/
def symbolicPower (P : Ideal R) (s : ℕ) : Ideal R :=
  Ideal.span {f | ∃ g : R, g ∉ P ∧ g * f ∈ P ^ s}

variable (P : Ideal R) [P.IsPrime] (s : ℕ)

/-- The exact unbounded denominator criterion for symbolic-power membership. -/
theorem mem_symbolicPower_iff (f : R) :
    f ∈ symbolicPower P s ↔ ∃ g : R, g ∉ P ∧ g * f ∈ P ^ s := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem f hf => exact hf
    | zero => exact ⟨1, P.one_notMem, by simp⟩
    | add f h hf hh ihf ihh =>
      obtain ⟨a, ha, haf⟩ := ihf
      obtain ⟨b, hb, hbh⟩ := ihh
      refine ⟨a * b, P.primeCompl.mul_mem ha hb, ?_⟩
      have h₁ := (P ^ s).mul_mem_left b haf
      have h₂ := (P ^ s).mul_mem_left a hbh
      convert (P ^ s).add_mem h₁ h₂ using 1 <;> ring
    | smul c f hf ih =>
      obtain ⟨a, ha, haf⟩ := ih
      refine ⟨a, ha, ?_⟩
      convert (P ^ s).mul_mem_left c haf using 1 <;> simp only [smul_eq_mul] <;> ring
  · intro hf
    exact Ideal.subset_span (α := R) hf

/-- Ordinary powers always lie in symbolic powers. -/
theorem pow_le_symbolicPower : P ^ s ≤ symbolicPower P s := by
  intro f hf
  apply (mem_symbolicPower_iff P s f).2
  exact ⟨1, P.one_notMem, by simpa using hf⟩

/-- Multiplying a symbolic-power element by a denominator outside the prime does not affect
membership, so this construction is precisely saturated at that complement. -/
theorem mul_mem_symbolicPower_iff {a f : R} (ha : a ∉ P) :
    a * f ∈ symbolicPower P s ↔ f ∈ symbolicPower P s := by
  constructor
  · intro h
    obtain ⟨b, hb, hbf⟩ := (mem_symbolicPower_iff P s (a * f)).1 h
    apply (mem_symbolicPower_iff P s f).2
    refine ⟨b * a, P.primeCompl.mul_mem hb ha, ?_⟩
    simpa only [mul_assoc] using hbf
  · exact (symbolicPower P s).mul_mem_left a

/-- The construction is the usual contraction of the ordinary power from the local ring. -/
theorem symbolicPower_eq_localization_comap :
    symbolicPower P s =
      Ideal.comap (algebraMap R (Localization.AtPrime P))
        (Ideal.map (algebraMap R (Localization.AtPrime P)) (P ^ s)) := by
  ext f
  rw [mem_symbolicPower_iff, Ideal.mem_comap,
    IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl]
  rfl

end FourPapers.Symmetric
end
end


/- SOURCE remote_SymbolicGenerators.lean -/
section

set_option autoImplicit false

/-!
# Exact generators for the symbolic conditions

The size is unrestricted in the type of minor data; impossible sizes are excluded only by
the requirement for increasing row and column embeddings. The symbolic score is exactly
the sum in Theorem 1.2, and the definition permits every number of factors.
-/

noncomputable section

namespace FourPapers.Symmetric

open MvPolynomial Finset
open scoped MonomialOrder

/-- Row and column data of an arbitrary minor. -/
structure MinorData (n : ℕ) where
  size : ℕ
  rows : Fin size ↪o Fin n
  cols : Fin size ↪o Fin n

namespace MinorData

variable {n : ℕ}

/-- The genuine determinant attached to a minor datum. -/
def polynomial (K : Type*) [CommRing K] (δ : MinorData n) : CoordinateRing n K :=
  minor K δ.rows δ.cols

/-- Its folded antidiagonal exponent. -/
def exponent (δ : MinorData n) : Entry n →₀ ℕ :=
  antidiagonalExponent δ.rows δ.cols

/-- Its sign under the prescribed order. -/
def leadingSign (K : Type*) [CommRing K] (δ : MinorData n) : K :=
  signCoefficient K (Fin.revPerm : Equiv.Perm (Fin δ.size))

theorem degree_polynomial (K : Type*) [CommRing K] [Nontrivial K] (δ : MinorData n) :
    (foldedOrder n).degree (δ.polynomial K) = δ.exponent :=
  minor_degree K δ.rows δ.cols

theorem leadingCoeff_polynomial (K : Type*) [CommRing K] (δ : MinorData n) :
    (foldedOrder n).leadingCoeff (δ.polynomial K) = δ.leadingSign K :=
  minor_leadingCoeff K δ.rows δ.cols

theorem leadingCoeff_polynomial_isUnit (K : Type*) [CommRing K] (δ : MinorData n) :
    IsUnit ((foldedOrder n).leadingCoeff (δ.polynomial K)) :=
  minor_leadingCoeff_isUnit K δ.rows δ.cols

end MinorData

variable {n : ℕ}

/-- The set `G_(n,t,s)` from the paper, with exact score `s`. -/
def symbolicGenerators (K : Type*) [CommRing K] (n t s : ℕ) :
    Set (CoordinateRing n K) :=
  {f | ∃ (k : ℕ) (δ : Fin k → MinorData n),
    (∀ j, t ≤ (δ j).size) ∧ (∑ j, ((δ j).size - t + 1)) = s ∧
    f = ∏ j, (δ j).polynomial K}

/-- The corresponding products of folded antidiagonals, with the same exact score. -/
def symbolicAntidiagonals (K : Type*) [CommRing K] (n t s : ℕ) :
    Set (CoordinateRing n K) :=
  {f | ∃ (k : ℕ) (δ : Fin k → MinorData n),
    (∀ j, t ≤ (δ j).size) ∧ (∑ j, ((δ j).size - t + 1)) = s ∧
    f = monomial (∑ j, (δ j).exponent) 1}

/-- The monomial ideal `J_(n,t,s)`. -/
def symbolicAntidiagonalIdeal (K : Type*) [CommRing K] (n t s : ℕ) :
    Ideal (CoordinateRing n K) := Ideal.span (symbolicAntidiagonals K n t s)

/-- The literal mixed generating set in Theorem 1.2. -/
def mixedGenerators (K : Type*) [CommRing K] (r : RankArray n)
    (conditions : List (ℕ × ℕ)) : Set (CoordinateRing n K) :=
  northwestGenerators K r ∪
    {f | ∃ ts ∈ conditions, f ∈ symbolicGenerators K n ts.1 ts.2}

/-- The ideal named on the left side of the field assertion of Theorem 1.2. This definition
uses actual symbolic powers, rather than defining them by the proposed generators. -/
def mixedIdeal (K : Type*) [CommRing K] (r : RankArray n)
    (conditions : List (ℕ × ℕ)) : Ideal (CoordinateRing n K) :=
  northwestIdeal K r + (conditions.map fun ts =>
    symbolicPower (determinantalIdeal n K ts.1) ts.2).sum

/-- All products of minors retain the product of the antidiagonal leading terms. -/
theorem product_minors_leadingTerm (K : Type*) [CommRing K] {k : ℕ}
    (δ : Fin k → MinorData n) :
    (foldedOrder n).leadingTerm (∏ j, (δ j).polynomial K) =
      monomial (∑ j, (δ j).exponent) (∏ j, (δ j).leadingSign K) := by
  classical
  rw [(foldedOrder n).leadingTerm_prod_of_regular]
  · simp only [MinorData.polynomial, minor_leadingTerm, MinorData.exponent,
      MinorData.leadingSign, ← monomial_sum_prod]
  · intro j _
    exact ((δ j).leadingCoeff_polynomial_isUnit K).isRegular

/-- The products in the proposed basis always have unit leading coefficients. -/
theorem product_minors_leadingCoeff_isUnit (K : Type*) [CommRing K] {k : ℕ}
    (δ : Fin k → MinorData n) :
    IsUnit ((foldedOrder n).leadingCoeff (∏ j, (δ j).polynomial K)) := by
  classical
  rw [(foldedOrder n).leadingCoeff_prod_of_regular]
  · apply IsUnit.of_mul_eq_one (∏ j, (δ j).leadingSign K)
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro j hj
    rw [MinorData.leadingCoeff_polynomial]
    exact signCoefficient_mul_self K _
  · intro j _
    exact ((δ j).leadingCoeff_polynomial_isUnit K).isRegular

end FourPapers.Symmetric
end
end


/- SOURCE remote_VariablePowerPrereq.lean -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Ideals of multivariate polynomial rings

Let `J` be the ideal of `R[X_i : i ∈ σ]` generated by the variables. It is the kernel of the
constant coefficient, and its powers are characterised by total degree.

The `k`-th power `J ^ k` consists of the polynomials all of whose monomials have total degree at
least `k` (`MvPolynomial.mem_pow_idealOfVars_iff`). This file records that multiplying an element of
`J ^ k` by any `q` only involves the constant coefficient of `q` in total degrees at most `k`.
This is how a linear map between free modules over `R[X_i : i ∈ σ]` acts, in the lowest degree
of the `J`-adic filtration, through its reduction modulo the variables. It also records that `J`
is maximal over a field.

For arbitrary ideals given by generating sets, adjoining one auxiliary variable reduces their
intersection to contraction: multiply the first family by `X none` and the second by
`1 - X none`, then contract along `rename some`. Similarly, the saturation of an ideal `I` by a
polynomial `f`, the set of `g` with `f ^ n * g ∈ I` for some `n`, is the contraction along
`rename some` of `I + (f X_none - 1)`; it is also the contraction of `I` from the localization
away from `f`. Likewise, the relations of a polynomial parametrization are the contraction of
its graph equations `Y i - f i`. These formulas need no monomial order.

## Main results

* `MvPolynomial.ker_constantCoeff`: the kernel of the constant coefficient is the ideal generated
  by the variables.
* `MvPolynomial.isMaximal_idealOfVars`: over a field, the ideal of the variables is maximal.
* `MvPolynomial.coeff_mul_of_mem_pow_idealOfVars`: for `p ∈ J ^ k` and a monomial `e` of total
  degree at most `k`, the coefficient of `e` in `p * q` is the coefficient of `e` in `p` times the
  constant coefficient of `q`.
* `MvPolynomial.ker_aeval_sumElim`: the graph equations generate the kernel of substitution
  which keeps the original variables.
* `MvPolynomial.ker_aeval_eq_comap_graph`: the relations among a family of polynomials are
  obtained by eliminating the original variables from its graph ideal.
* `Ideal.span_inf_span_eq_comap_rename_some`: an intersection of generated ideals is the
  contraction of an ideal in one more variable.
* `Ideal.mem_comap_rename_some_map_rename_some_sup_span_iff` and
  `Ideal.comap_rename_some_map_rename_some_sup_span`: the saturation of an ideal by a polynomial is
  the contraction of an ideal in one more variable, and the contraction from the localization.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 4, §3,
  computing intersections by elimination; Chapter 4, §4, computing saturations by
  elimination; Chapter 3, §3, implicitization by elimination.
-/

section

namespace MvPolynomial

open Finsupp

variable {R σ : Type*} [CommSemiring R]

variable (σ R) in
/-- The kernel of the constant coefficient is the ideal generated by the variables. -/
theorem ker_constantCoeff : RingHom.ker (constantCoeff (σ := σ) (R := R)) = idealOfVars σ R := by
  ext p
  rw [RingHom.mem_ker, ← pow_one (idealOfVars σ R), mem_pow_idealOfVars_iff', constantCoeff_eq]
  simp [degree_eq_zero_iff]

/-- Over a field, the ideal generated by all variables is maximal. -/
instance isMaximal_idealOfVars (σ K : Type*) [Field K] : (idealOfVars σ K).IsMaximal := by
  rw [← ker_constantCoeff]
  exact RingHom.ker_isMaximal_of_surjective (constantCoeff : MvPolynomial σ K →+* K)
    (fun scalar ↦ ⟨C scalar, by simp⟩)

/-- If `p` lies in the `k`-th power of the ideal generated by the variables, then the coefficients
of `p * q` in total degree at most `k` are those of `p` times the constant coefficient of `q`. -/
theorem coeff_mul_of_mem_pow_idealOfVars (p : MvPolynomial σ R) {k : ℕ}
    (hp : p ∈ idealOfVars σ R ^ k) (q : MvPolynomial σ R) {e : σ →₀ ℕ} (he : degree e ≤ k) :
    (p * q).coeff e = p.coeff e * constantCoeff q := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (e, 0), constantCoeff_eq]
  · rintro ⟨a, b⟩ hab hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    have hb : degree b ≠ 0 := by
      rw [Ne, degree_eq_zero_iff]
      rintro rfl
      exact hne (by simp_all)
    have hdeg : degree a + degree b = degree e := by rw [← map_add, hab]
    rw [(mem_pow_idealOfVars_iff' k p).mp hp a (by omega), zero_mul]
  · exact fun h ↦ absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_zero e)) h

end MvPolynomial
end

end


/- SOURCE archive_VariablePower.lean -/
section

set_option autoImplicit false

/-!
# Powers of independent variables over a domain

The symbolic Schur chart uses a polynomial ring in the residual symmetric entries over a
coefficient domain. This file proves the exact cancellation property needed in that chart:
multiplication by a polynomial with nonzero constant coefficient does not change membership
in any power of the ideal of the residual variables. The variables and exponent are arbitrary.
-/

namespace FourPapers.Symmetric

open MvPolynomial

variable {σ R : Type*} [CommRing R] [IsDomain R]

/-- The residual-variable ideal is prime over any coefficient domain. -/
theorem idealOfVars_isPrime : (idealOfVars σ R).IsPrime := by
  rw [← MvPolynomial.ker_constantCoeff]
  exact RingHom.ker_isPrime _

/-- The coefficient-domain hypothesis is exactly what permits cancellation in the first
nonzero homogeneous component. -/
theorem mem_pow_idealOfVars_of_mul {p q : MvPolynomial σ R}
    (hq : constantCoeff q ≠ 0) (s : ℕ)
    (hpq : p * q ∈ idealOfVars σ R ^ s) : p ∈ idealOfVars σ R ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hps : p ∈ idealOfVars σ R ^ s :=
      ih (Ideal.pow_le_pow_right (Nat.le_succ s) hpq)
    rw [mem_pow_idealOfVars_iff']
    intro e he
    have hz := (mem_pow_idealOfVars_iff' (s + 1) (p * q)).mp hpq e he
    rw [coeff_mul_of_mem_pow_idealOfVars p hps q (Nat.lt_succ_iff.mp he)] at hz
    exact (mul_eq_zero.mp hz).resolve_right hq

/-- Cancellation holds for every denominator outside the residual-variable prime. -/
theorem mul_mem_pow_idealOfVars_iff {p q : MvPolynomial σ R}
    (hq : q ∉ idealOfVars σ R) (s : ℕ) :
    q * p ∈ idealOfVars σ R ^ s ↔ p ∈ idealOfVars σ R ^ s := by
  constructor
  · intro h
    have hc : constantCoeff q ≠ 0 := by
      simpa only [← MvPolynomial.ker_constantCoeff, RingHom.mem_ker] using hq
    exact mem_pow_idealOfVars_of_mul hc s (by simpa only [mul_comm] using h)
  · exact (idealOfVars σ R ^ s).mul_mem_left q

/-- Thus ordinary powers in the polynomial chart already equal their symbolic powers. -/
theorem symbolicPower_idealOfVars (s : ℕ) :
    symbolicPower (idealOfVars σ R) s = idealOfVars σ R ^ s := by
  letI : (idealOfVars σ R).IsPrime := idealOfVars_isPrime
  apply le_antisymm
  · intro p hp
    obtain ⟨q, hq, hqp⟩ := (mem_symbolicPower_iff (idealOfVars σ R) s p).mp hp
    exact (mul_mem_pow_idealOfVars_iff hq s).mp hqp
  · exact pow_le_symbolicPower (idealOfVars σ R) s

end FourPapers.Symmetric
end


/- SOURCE remote_SingletonMinors.lean -/
section
namespace FourPapers.Symmetric
open MvPolynomial
variable {n : ℕ}
/-- The one-entry increasing list. -/
def singletonEmbedding (i : Fin n) : Fin 1 ↪o Fin n :=
  OrderEmbedding.ofStrictMono (fun _ => i) (Subsingleton.strictMono _)

@[simp] theorem minor_singleton (K : Type*) [CommRing K] (i j : Fin n) :
    minor K (singletonEmbedding i) (singletonEmbedding j) = X (fold i j) := by
  simp [minor, Matrix.det_fin_one, singletonEmbedding]


end FourPapers.Symmetric

end


/- SOURCE DeterminantalBasic.lean -/
section
set_option autoImplicit false
namespace FourPapers.Symmetric
open MvPolynomial
theorem fullMinorGenerators_succ_eq_northwest (n : ℕ) (K : Type*) [CommRing K]
    (t : ℕ) :
    fullMinorGenerators n K (t + 1) = northwestGenerators K (fun _ _ => t) := by
  classical
  cases n with
  | zero =>
    ext f
    constructor
    · rintro ⟨a, b, hf⟩
      exact Fin.elim0 (a 0)
    · rintro ⟨i, j, a, b, ha, hb, hf⟩
      exact Fin.elim0 i
  | succ n =>
    ext f
    constructor
    · rintro ⟨a, b, rfl⟩
      exact ⟨Fin.last n, Fin.last n, a, b,
        fun _ => Fin.le_last _, fun _ => Fin.le_last _, rfl⟩
    · rintro ⟨i, j, a, b, ha, hb, rfl⟩
      exact ⟨a, b, rfl⟩

theorem determinantalIdeal_succ_eq_northwest (n : ℕ) (K : Type*) [CommRing K]
    (t : ℕ) :
    determinantalIdeal n K (t + 1) = northwestIdeal K (fun _ _ => t) := by
  rw [determinantalIdeal, fullMinorGenerators_succ_eq_northwest]
  rfl

theorem determinantalIdeal_one (n : ℕ) (K : Type*) [CommRing K] :
    determinantalIdeal n K 1 = idealOfVars (Entry n) K := by
  have hG : fullMinorGenerators n K 1 = Set.range (X : Entry n → CoordinateRing n K) := by
    ext f
    constructor
    · rintro ⟨a, b, rfl⟩
      exact ⟨fold (a 0) (b 0), by simp [minor, Matrix.det_fin_one]⟩
    · rintro ⟨e, rfl⟩
      refine ⟨singletonEmbedding e.val.1, singletonEmbedding e.val.2, ?_⟩
      rw [minor_singleton]
      congr 1
      apply Subtype.ext
      simp only [fold, max_eq_left e.property, min_eq_right e.property]
      rfl
  rw [determinantalIdeal, hG]


end FourPapers.Symmetric

end


/- SOURCE SymbolicGeneratorLeading.lean -/
section
set_option autoImplicit false
namespace FourPapers.Symmetric
theorem symbolicGenerators_unit_leading (R : Type*) [CommRing R] (n t s : ℕ) :
    ∀ g ∈ symbolicGenerators R n t s,
      g ≠ 0 → IsUnit ((foldedOrder n).leadingCoeff g) := by
  rintro _ ⟨k, δ, hsize, hscore, rfl⟩ _
  exact product_minors_leadingCoeff_isUnit R δ

end FourPapers.Symmetric

end


/- SOURCE TotalDegreeSymbolic.lean -/
section

set_option autoImplicit false

/-! # The size-one symbolic condition

The first determinantal ideal is the coordinate maximal ideal.  Its symbolic
powers are its ordinary powers.  Every degree-s monomial is exhibited as a
literal product of s one-by-one minors, and the larger minors in the proposed
family are homogeneous of the same total degree.  This proves the complete
size-one Gröbner assertion without an extra matrix-size restriction.
-/

noncomputable section

namespace FourPapers.Symmetric

open MvPolynomial

/-- Every exponent is a finite sum of its individual variable occurrences. -/
theorem exists_sum_single_one {σ : Type*} (e : σ →₀ ℕ) :
    ∃ f : Fin e.degree → σ, ∑ i, Finsupp.single (f i) 1 = e := by
  classical
  suffices ∀ (d : ℕ) (e : σ →₀ ℕ), e.degree = d →
      ∃ f : Fin d → σ, ∑ i, Finsupp.single (f i) 1 = e from this e.degree e rfl
  intro d
  induction d with
  | zero =>
    intro e he
    have he0 : e = 0 := (Finsupp.degree_eq_zero_iff e).mp he
    exact ⟨Fin.elim0, by simp [he0]⟩
  | succ d ih =>
    intro e he
    obtain ⟨i, hi⟩ : e.support.Nonempty := by
      rw [Finsupp.support_nonempty_iff]
      intro hz
      simp [hz] at he
    let e' := e - Finsupp.single i 1
    have hsum : e' + Finsupp.single i 1 = e := by
      apply Finsupp.sub_add_single_one_cancel
      rwa [← Finsupp.mem_support_iff]
    have hdegree : e'.degree = d := by
      have h := congrArg Finsupp.degree hsum
      simp only [map_add, Finsupp.degree_single] at h
      omega
    obtain ⟨f, hf⟩ := ih e' hdegree
    refine ⟨Fin.cons i f, ?_⟩
    simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hf, add_comm] using hsum

theorem minor_isHomogeneous_total {n t : ℕ} (K : Type*) [CommRing K]
    (a b : Fin t ↪o Fin n) : (minor K a b).IsHomogeneous t := by
  classical
  unfold minor
  rw [Matrix.det_apply']
  apply IsHomogeneous.sum
  intro π hπ
  have hp : IsHomogeneous
      (∏ i : Fin t, (genericMatrix n K).submatrix a b (π i) i) t := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one] using IsHomogeneous.prod Finset.univ
      (fun i : Fin t => (genericMatrix n K).submatrix a b (π i) i)
      (fun _ => 1) (fun i _ => isHomogeneous_X K (fold (a (π i)) (b i)))
  convert hp.C_mul (((Equiv.Perm.sign π : ℤ) : K)) using 1 <;>
    simp

theorem product_minors_isHomogeneous_total {n k : ℕ} (K : Type*) [CommRing K]
    (δ : Fin k → MinorData n) :
    (∏ j, (δ j).polynomial K).IsHomogeneous (∑ j, (δ j).size) :=
  IsHomogeneous.prod Finset.univ _ _ (fun j _ => minor_isHomogeneous_total K _ _)

theorem monomial_mem_symbolicGenerators_one {n s : ℕ} (K : Type*) [CommRing K]
    (e : Entry n →₀ ℕ) (he : e.degree = s) :
    monomial e (1 : K) ∈ symbolicGenerators K n 1 s := by
  classical
  obtain ⟨f, hf⟩ := exists_sum_single_one e
  let δ : Fin e.degree → MinorData n := fun j =>
    ⟨1, singletonEmbedding (f j).val.1, singletonEmbedding (f j).val.2⟩
  have hδ : ∀ j, (δ j).polynomial K = X (f j) := by
    intro j
    rw [MinorData.polynomial, minor_singleton]
    congr 1
    apply Subtype.ext
    simp only [fold, max_eq_left (f j).property, min_eq_right (f j).property]
    rfl
  refine ⟨e.degree, δ, fun _ => le_rfl, ?_, ?_⟩
  · simpa [δ] using he
  · simp_rw [hδ, MvPolynomial.X]
    rw [← monomial_sum_prod, hf]
    simp

theorem symbolicGenerators_one_isHomogeneous {n s : ℕ} (K : Type*) [CommRing K]
    {f : CoordinateRing n K} (hf : f ∈ symbolicGenerators K n 1 s) :
    f.IsHomogeneous s := by
  obtain ⟨k, δ, hsize, hscore, rfl⟩ := hf
  have hsizes : ∑ j, (δ j).size = s := by
    rw [← hscore]
    apply Finset.sum_congr rfl
    intro j hj
    have := hsize j
    omega
  rw [← hsizes]
  exact product_minors_isHomogeneous_total K δ

theorem symbolicGenerators_one_subset_pow {n s : ℕ} (K : Type*) [CommRing K] :
    symbolicGenerators K n 1 s ⊆ ((idealOfVars (Entry n) K ^ s :
      Ideal (CoordinateRing n K)) : Set (CoordinateRing n K)) := by
  intro f hf
  change f ∈ idealOfVars (Entry n) K ^ s
  rw [mem_pow_idealOfVars_iff]
  intro e he
  have hd := symbolicGenerators_one_isHomogeneous K hf (mem_support_iff.mp he)
  have : e.degree = s := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd
  exact this.ge

/-- Every size-one symbolic generator family is a Gröbner basis for the actual
symbolic power over every coefficient domain. -/
theorem symbolicGenerators_one_groebner (n : ℕ) (K : Type*) [CommRing K] [IsDomain K]
    (s : ℕ) :
    (foldedOrder n).IsGroebnerBasis (symbolicGenerators K n 1 s)
      (symbolicPower (determinantalIdeal n K 1) s) := by
  classical
  rw [determinantalIdeal_one, symbolicPower_idealOfVars]
  apply (MonomialOrder.isGroebnerBasis_iff_forall_exists_degree_le_degree
    (symbolicGenerators_unit_leading K n 1 s)).mpr
  refine ⟨symbolicGenerators_one_subset_pow K, ?_⟩
  intro f hf hf0
  have hd : s ≤ ((foldedOrder n).degree f).degree :=
    (mem_pow_idealOfVars_iff s f).mp hf _ ((foldedOrder n).degree_mem_support hf0)
  obtain ⟨e, he, hes⟩ := Finsupp.exists_le_degree_eq ((foldedOrder n).degree f) s hd
  refine ⟨monomial e 1, monomial_mem_symbolicGenerators_one K e hes, ?_, ?_⟩
  · simp
  · simpa only [(foldedOrder n).degree_monomial, one_ne_zero, ↓reduceIte] using he

end FourPapers.Symmetric

end
end


/- SOURCE ZeroVariableGroebnerExtension.lean -/
section

set_option autoImplicit false

/-!
# Adjoining a compatible set of coordinate variables

The hypothesis is the precise compatibility used for a northwest zero region:
a basis element whose leading monomial contains one of the selected variables
already lies in their ideal.  No restriction is made on the other terms.
-/

noncomputable section

open MvPolynomial

namespace MonomialOrder

variable {σ R : Type*} [CommRing R] [Nontrivial R]
  {m : MonomialOrder σ} {G : Set (MvPolynomial σ R)}
  {I : Ideal (MvPolynomial σ R)}

theorem criticalDegreeSpan_generators_mono {G H : Set (MvPolynomial σ R)}
    (hGH : G ⊆ H) (s : Set m.syn) :
    criticalDegreeSpan m G s ≤ criticalDegreeSpan m H s := by
  apply Submodule.span_mono
  rintro _ ⟨g, hg, a, ha, rfl⟩
  exact ⟨g, hGH hg, a, ha, rfl⟩

theorem isGroebnerBasis_variables (S : Set σ) :
    m.IsGroebnerBasis (X '' S) (Ideal.span (X '' S : Set (MvPolynomial σ R))) := by
  apply (isGroebnerBasis_iff_forall_exists_degree_le_degree
    (fun _ hg _ => ?_)).mpr
  · refine ⟨Ideal.subset_span, ?_⟩
    intro f hf hf0
    obtain ⟨i, hi, hdi⟩ := mem_ideal_span_X_image.mp hf
      (m.degree f) (m.degree_mem_support hf0)
    refine ⟨X i, ⟨i, hi, rfl⟩, X_ne_zero i, ?_⟩
    rw [m.degree_X]
    exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hdi)
  · obtain ⟨i, hi, rfl⟩ := hg
    simp only [m.leadingCoeff_X, isUnit_one]

/-- A critical pair with a selected variable belongs to the variable ideal. -/
theorem sPolynomial_variable_mem_span {f : MvPolynomial σ R}
    (S : Set σ) {i : σ} (hi : i ∈ S)
    (hcompat : m.degree f i ≠ 0 → f ∈ Ideal.span (X '' S : Set (MvPolynomial σ R))) :
    m.sPolynomial f (X i) ∈ Ideal.span (X '' S : Set (MvPolynomial σ R)) := by
  classical
  let J := Ideal.span (X '' S : Set (MvPolynomial σ R))
  have hX : X i ∈ J := Ideal.subset_span ⟨i, hi, rfl⟩
  rw [sPolynomial]
  apply J.sub_mem
  · by_cases hd : m.degree f i = 0
    · have hm : monomial (m.degree (X i : MvPolynomial σ R) - m.degree f)
          (m.leadingCoeff (X i : MvPolynomial σ R)) ∈ J := by
        rw [m.degree_X, m.leadingCoeff_X]
        apply mem_ideal_span_X_image.mpr
        intro e he
        have heq : e = Finsupp.single i 1 - m.degree f := by
          simpa only [support_monomial, one_ne_zero, if_false, Finset.mem_singleton] using he
        subst e
        exact ⟨i, hi, by simp [Finsupp.tsub_apply, hd]⟩
      exact J.mul_mem_right f hm
    · exact J.mul_mem_left _ (hcompat hd)
  · exact J.mul_mem_left _ hX

theorem IsGroebnerBasis.adjoin_variables (hG : m.IsGroebnerBasis G I)
    (hunit : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) (S : Set σ)
    (hcompat : ∀ g ∈ G, (∃ i ∈ S, m.degree g i ≠ 0) →
      g ∈ Ideal.span (X '' S : Set (MvPolynomial σ R))) :
    m.IsGroebnerBasis (G ∪ X '' S)
      (I ⊔ Ideal.span (X '' S : Set (MvPolynomial σ R))) := by
  classical
  let H : Set (MvPolynomial σ R) := X '' S
  let J : Ideal (MvPolynomial σ R) := Ideal.span H
  have hH : m.IsGroebnerBasis H J := isGroebnerBasis_variables S
  have hUH : G ∪ H = G ∪ X '' S := rfl
  have hspan : Ideal.span (G ∪ H) = I ⊔ J := by
    rw [Ideal.span_union, ← hG.ideal_eq_span]
  rw [← hspan]
  apply isGroebnerBasis_span_of_sPolynomial_mem_criticalDegreeSpan
  · intro g hg hg0
    rcases hg with hg | ⟨i, hi, rfl⟩
    · exact hunit g hg hg0
    · simp only [m.leadingCoeff_X, isUnit_one]
  · intro f hf g hg
    have liftG := criticalDegreeSpan_generators_mono (m := m)
      (show G ⊆ G ∪ H from Set.subset_union_left)
    have liftH := criticalDegreeSpan_generators_mono (m := m)
      (show H ⊆ G ∪ H from Set.subset_union_right)
    have hpair (a b : MvPolynomial σ R)
        (hab : m.sPolynomial a b ∈ J) :
        m.sPolynomial a b ∈ criticalDegreeSpan m (G ∪ H)
          (Set.Iio (m.toSyn (m.degree a ⊔ m.degree b))) := by
      by_cases hz : m.sPolynomial a b = 0
      · simp [hz]
      exact liftH _ (criticalDegreeSpan_mono
        (Set.Iic_subset_Iio.mpr (m.degree_sPolynomial_lt_sup_degree hz))
        (hH.isRemainder_zero_iff_mem.mpr hab).mem_criticalDegreeSpan)
    rcases hf with hf | ⟨i, hi, rfl⟩
    · rcases hg with hg | ⟨j, hj, rfl⟩
      · exact liftG _ (hG.sPolynomial_mem_criticalDegreeSpan hf hg)
      · apply hpair
        exact sPolynomial_variable_mem_span S hj
          (fun hd => hcompat f hf ⟨j, hj, hd⟩)
    · rcases hg with hg | ⟨j, hj, rfl⟩
      · apply hpair
        have hs : m.sPolynomial g (X i) ∈ J :=
          sPolynomial_variable_mem_span S hi
            (fun hd => hcompat g hg ⟨i, hi, hd⟩)
        have heq : m.sPolynomial (X i) g = -m.sPolynomial g (X i) := by
          simp only [sPolynomial, neg_sub]
        exact heq ▸ J.neg_mem hs
      · exact liftH _ (hH.sPolynomial_mem_criticalDegreeSpan
          ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩)

end MonomialOrder

end
end


/- SOURCE remote_FerrersVanishing.lean -/
section

set_option autoImplicit false

/-!
# Zero northwest rectangles

The zero-bound reduction rests on a pigeonhole statement: every permutation term of a
minor meets the northwest rectangle determined by any one of its antidiagonal positions.
Consequently a minor whose antidiagonal meets a northwest closed zero region lies in the
ideal of that region's variables. This argument works over every commutative coefficient ring.
-/

noncomputable section

namespace FourPapers.Symmetric

open Finset MvPolynomial

/-- The selected northwest rectangle has one more row-plus-column than the ambient size,
so every permutation meets it. -/
theorem permutation_meets_antidiagonal_prefix {t : ℕ}
    (σ : Equiv.Perm (Fin t)) (p : Fin t) :
    ∃ i : Fin t, i ≤ p.rev ∧ σ i ≤ p := by
  classical
  by_contra hn
  push Not at hn
  have hmap : ∀ i ∈ Iic p.rev, σ i ∈ Ioi p := by
    intro i hi
    exact mem_Ioi.mpr (hn i (mem_Iic.mp hi))
  have hcard := Finset.card_le_card_of_injOn σ hmap
    (fun _ _ _ _ h => σ.injective h)
  rw [Fin.card_Iic, Fin.card_Ioi] at hcard
  simp only [Fin.val_rev] at hcard
  omega

/-- A determinant is in an ideal as soon as a sufficiently large northwest rectangle of
its entries lies in the ideal. The sizes are encoded by one antidiagonal position. -/
theorem determinant_mem_of_antidiagonal_prefix {t : ℕ} {R : Type*} [CommRing R]
    (I : Ideal R) (M : Matrix (Fin t) (Fin t) R) (p : Fin t)
    (hrect : ∀ i j, i ≤ p → j ≤ p.rev → M i j ∈ I) : M.det ∈ I := by
  classical
  rw [Matrix.det_apply']
  apply I.sum_mem
  intro σ _
  apply I.mul_mem_left
  obtain ⟨i, hi, hσi⟩ := permutation_meets_antidiagonal_prefix σ p
  rw [← Finset.prod_erase_mul _ _ (mem_univ i)]
  exact I.mul_mem_left _ (hrect (σ i) i hσi hi)

/-- A set of zero entries closed under passing northwest. Symmetry is not needed for this
individual vanishing lemma. -/
def NorthwestClosed {n : ℕ} (Z : Set (Fin n × Fin n)) : Prop :=
  ∀ ⦃i j i' j' : Fin n⦄, i' ≤ i → j' ≤ j → (i, j) ∈ Z → (i', j') ∈ Z

/-- The ideal of the actual independent symmetric variables in a region of positions. -/
def zeroVariableIdeal {n : ℕ} (K : Type*) [CommRing K]
    (Z : Set (Fin n × Fin n)) : Ideal (CoordinateRing n K) :=
  Ideal.span {f | ∃ i j, (i, j) ∈ Z ∧ f = X (fold i j)}

/-- The vanishing assertion used to adjoin zero-bound variables in Proposition 4.1 and
Theorem 1.2. No matrix size or characteristic has been restricted. -/
theorem minor_mem_zeroVariableIdeal {n t : ℕ} (K : Type*) [CommRing K]
    {Z : Set (Fin n × Fin n)} (hZ : NorthwestClosed Z)
    (a b : Fin t ↪o Fin n) (p : Fin t) (hp : (a p, b p.rev) ∈ Z) :
    minor K a b ∈ zeroVariableIdeal K Z := by
  apply determinant_mem_of_antidiagonal_prefix (zeroVariableIdeal K Z)
    ((genericMatrix n K).submatrix a b) p
  intro i j hi hj
  apply Ideal.subset_span
  exact ⟨a i, b j, hZ (a.monotone hi) (b.monotone hj) hp, rfl⟩

/-- An independent coordinate occurs in the folded antidiagonal exactly when one of the
selected antidiagonal positions folds to it. -/
theorem antidiagonalExponent_pos_iff {n t : ℕ} (a b : Fin t ↪o Fin n) (e : Entry n) :
    0 < antidiagonalExponent a b e ↔ ∃ p : Fin t, fold (a p) (b p.rev) = e := by
  classical
  simp [antidiagonalExponent, Finset.sum_apply', Finset.sum_pos_iff, Finsupp.single_apply]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa using hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa using hx⟩

/-- The preceding vanishing conclusion in the paper's folded-variable formulation. -/
theorem minor_mem_zeroVariableIdeal_of_antidiagonal_meets {n t : ℕ}
    (K : Type*) [CommRing K] {Z : Set (Fin n × Fin n)}
    (hZ : NorthwestClosed Z) (hsym : ∀ i j, (i, j) ∈ Z → (j, i) ∈ Z)
    (a b : Fin t ↪o Fin n) {i j : Fin n}
    (hij : (i, j) ∈ Z) (hpos : 0 < antidiagonalExponent a b (fold i j)) :
    minor K a b ∈ zeroVariableIdeal K Z := by
  obtain ⟨p, hp⟩ := (antidiagonalExponent_pos_iff a b (fold i j)).mp hpos
  apply minor_mem_zeroVariableIdeal K hZ a b p
  rcases (fold_eq_iff (a p) (b p.rev) i j).mp hp with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simpa only [ha, hb] using hij
  · simpa only [ha, hb] using hsym i j hij

end FourPapers.Symmetric
end
end


/- SOURCE remote_ZeroBounds.lean -/
section

set_option autoImplicit false

/-!
# Exact reduction of zero northwest bounds

Replacing each zero bound by one introduces only minors already killed by the zero-bound
variables. The resulting ideal identity is proved for every rank array and coefficient ring.
-/

namespace FourPapers.Symmetric

open MvPolynomial Finset

variable {n : ℕ}

/-- The array in which zero bounds have been replaced by one. -/
def positiveBounds (r : RankArray n) : RankArray n := fun i j => max (r i j) 1

/-- The union of the northwest rectangles required to have rank zero. -/
def zeroRegion (r : RankArray n) : Set (Fin n × Fin n) :=
  {p | ∃ i j, r i j = 0 ∧ p.1 ≤ i ∧ p.2 ≤ j}

theorem zeroRegion_northwestClosed (r : RankArray n) : NorthwestClosed (zeroRegion r) := by
  intro i j i' j' hi hj h
  obtain ⟨a, b, hab, hia, hjb⟩ := h
  exact ⟨a, b, hab, hi.trans hia, hj.trans hjb⟩

theorem zeroRegion_symmetric {r : RankArray n} (hr : ∀ i j, r i j = r j i) :
    ∀ i j, (i, j) ∈ zeroRegion r → (j, i) ∈ zeroRegion r := by
  rintro i j ⟨a, b, hab, hia, hjb⟩
  exact ⟨b, a, (hr b a).trans hab, hjb, hia⟩

theorem variable_mem_northwestIdeal_of_zero_bound (K : Type*) [CommRing K]
    (r : RankArray n) {i j a b : Fin n} (hr : r a b = 0) (hi : i ≤ a) (hj : j ≤ b) :
    X (fold i j) ∈ northwestIdeal K r := by
  apply Ideal.subset_span
  refine ⟨a, b, ?_⟩
  rw [hr]
  exact ⟨singletonEmbedding i, singletonEmbedding j, fun _ => hi, fun _ => hj,
    (minor_singleton K i j).symm⟩

theorem zeroVariableIdeal_le_northwestIdeal (K : Type*) [CommRing K] (r : RankArray n) :
    zeroVariableIdeal K (zeroRegion r) ≤ northwestIdeal K r := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, j, ⟨a, b, hab, hia, hjb⟩, rfl⟩
  exact variable_mem_northwestIdeal_of_zero_bound K r hab hia hjb

private theorem prescribed_minor_mem_of_eq (K : Type*) [CommRing K]
    {r r' : RankArray n} (i j : Fin n) (h : r' i j = r i j)
    (a b : Fin (r i j + 1) ↪o Fin n) (ha : ∀ p, a p ≤ i) (hb : ∀ p, b p ≤ j) :
    minor K a b ∈ northwestIdeal K r' := by
  apply Ideal.subset_span
  refine ⟨i, j, ?_⟩
  rw [h]
  exact ⟨a, b, ha, hb, rfl⟩

private theorem minor_mem_zero_region (K : Type*) [CommRing K]
    (r : RankArray n) {i j : Fin n} (hr : r i j = 0) {t : ℕ}
    (a b : Fin (t + 1) ↪o Fin n) (ha : ∀ p, a p ≤ i) (hb : ∀ p, b p ≤ j) :
    minor K a b ∈ zeroVariableIdeal K (zeroRegion r) := by
  let p : Fin (t + 1) := 0
  exact minor_mem_zeroVariableIdeal K (zeroRegion_northwestClosed r) a b p
    ⟨i, j, hr, ha p, hb p.rev⟩

/-- Increasing a zero bound to one does not enlarge the ideal. -/
theorem northwestIdeal_positiveBounds_le (K : Type*) [CommRing K] (r : RankArray n) :
    northwestIdeal K (positiveBounds r) ≤ northwestIdeal K r := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, j, a, b, ha, hb, rfl⟩
  by_cases hr : r i j = 0
  · exact zeroVariableIdeal_le_northwestIdeal K r (minor_mem_zero_region K r hr a b ha hb)
  · have h : positiveBounds r i j = r i j :=
      max_eq_left (Nat.one_le_iff_ne_zero.mpr hr)
    exact prescribed_minor_mem_of_eq K i j h.symm a b ha hb

/-- The exact zero-bound ideal identity in Proposition 4.1. -/
theorem northwestIdeal_zero_bound_reduction (K : Type*) [CommRing K] (r : RankArray n) :
    northwestIdeal K r = northwestIdeal K (positiveBounds r) ⊔
      zeroVariableIdeal K (zeroRegion r) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, j, a, b, ha, hb, rfl⟩
    by_cases hr : r i j = 0
    · exact (show zeroVariableIdeal K (zeroRegion r) ≤
        northwestIdeal K (positiveBounds r) ⊔ zeroVariableIdeal K (zeroRegion r) from le_sup_right)
        (minor_mem_zero_region K r hr a b ha hb)
    · have h : positiveBounds r i j = r i j :=
        max_eq_left (Nat.one_le_iff_ne_zero.mpr hr)
      exact (show northwestIdeal K (positiveBounds r) ≤
        northwestIdeal K (positiveBounds r) ⊔ zeroVariableIdeal K (zeroRegion r) from le_sup_left)
        (prescribed_minor_mem_of_eq K i j h a b ha hb)
  · exact sup_le (northwestIdeal_positiveBounds_le K r)
      (zeroVariableIdeal_le_northwestIdeal K r)

end FourPapers.Symmetric
end


/- SOURCE MixedZeroBounds.lean -/
section

set_option autoImplicit false

/-!
# The zero-bound step for every mixed symbolic condition

All products in the proposed symbolic families satisfy the same Ferrers
vanishing property as one determinant.  Adjoining the actual zero-bound
coordinates therefore preserves the Gröbner basis.  The auxiliary minors
introduced by changing zero bounds to one are then replaced by original
one-by-one generators, using divisibility in the coordinate ideal.
-/

noncomputable section

namespace FourPapers.Symmetric

open MvPolynomial

def zeroCoordinates {n : ℕ} (Z : Set (Fin n × Fin n)) : Set (Entry n) :=
  (fun p => fold p.1 p.2) '' Z

theorem zeroVariableIdeal_eq_span_image {n : ℕ} (K : Type*) [CommRing K]
    (Z : Set (Fin n × Fin n)) :
    zeroVariableIdeal K Z = Ideal.span (X '' zeroCoordinates Z : Set (CoordinateRing n K)) := by
  unfold zeroVariableIdeal
  congr 1
  ext f
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    exact ⟨fold i j, ⟨(i, j), hij, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨⟨i, j⟩, hij, rfl⟩, rfl⟩
    exact ⟨i, j, hij, rfl⟩

theorem product_minors_degree {n k : ℕ} (K : Type*) [CommRing K] [Nontrivial K]
    (δ : Fin k → MinorData n) :
    (foldedOrder n).degree (∏ j, (δ j).polynomial K) = ∑ j, (δ j).exponent := by
  rw [(foldedOrder n).degree_prod_of_regular]
  · simp only [MinorData.degree_polynomial]
  · intro j hj
    exact ((δ j).leadingCoeff_polynomial_isUnit K).isRegular

theorem product_minors_mem_zeroVariableIdeal_of_degree {n k : ℕ}
    (K : Type*) [CommRing K] [Nontrivial K] (δ : Fin k → MinorData n)
    {Z : Set (Fin n × Fin n)} (hZ : NorthwestClosed Z)
    (hsym : ∀ i j, (i, j) ∈ Z → (j, i) ∈ Z)
    {e : Entry n} (he : e ∈ zeroCoordinates Z)
    (hd : (foldedOrder n).degree (∏ j, (δ j).polynomial K) e ≠ 0) :
    (∏ j, (δ j).polynomial K) ∈ zeroVariableIdeal K Z := by
  classical
  obtain ⟨⟨i, j⟩, hij, rfl⟩ := he
  have hpos : 0 < ∑ a : Fin k, (δ a).exponent (fold i j) := by
    simpa only [product_minors_degree, Finset.sum_apply'] using Nat.pos_of_ne_zero hd
  obtain ⟨a, ha, hpa⟩ := Finset.sum_pos_iff.mp hpos
  have hminor : (δ a).polynomial K ∈ zeroVariableIdeal K Z :=
    minor_mem_zeroVariableIdeal_of_antidiagonal_meets K hZ hsym
      (δ a).rows (δ a).cols hij hpa
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
  exact (zeroVariableIdeal K Z).mul_mem_left _ hminor

theorem mixedGenerators_ferrers_compatible {n : ℕ} (K : Type*)
    [CommRing K] [Nontrivial K] (r : RankArray n) (conditions : List (ℕ × ℕ))
    {Z : Set (Fin n × Fin n)} (hZ : NorthwestClosed Z)
    (hsym : ∀ i j, (i, j) ∈ Z → (j, i) ∈ Z) :
    ∀ g ∈ mixedGenerators K r conditions,
      (∃ e ∈ zeroCoordinates Z, (foldedOrder n).degree g e ≠ 0) →
      g ∈ zeroVariableIdeal K Z := by
  rintro g (hg | hg) ⟨e, he, hd⟩
  · obtain ⟨i, j, a, b, ha, hb, rfl⟩ := hg
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := he
    rw [minor_degree] at hd
    exact minor_mem_zeroVariableIdeal_of_antidiagonal_meets K hZ hsym a b
      huv (Nat.pos_of_ne_zero hd)
  · obtain ⟨ts, hts, k, δ, hsize, hscore, rfl⟩ := hg
    exact product_minors_mem_zeroVariableIdeal_of_degree K δ hZ hsym he hd

theorem mixedGenerators_unit_leading {n : ℕ} (K : Type*) [CommRing K]
    (r : RankArray n) (conditions : List (ℕ × ℕ)) :
    ∀ g ∈ mixedGenerators K r conditions,
      g ≠ 0 → IsUnit ((foldedOrder n).leadingCoeff g) := by
  rintro g (hg | hg) _
  · obtain ⟨i, j, a, b, ha, hb, rfl⟩ := hg
    exact minor_leadingCoeff_isUnit K a b
  · obtain ⟨ts, hts, k, δ, hsize, hscore, rfl⟩ := hg
    exact product_minors_leadingCoeff_isUnit K δ

theorem zeroCoordinates_variables_subset_northwestGenerators {n : ℕ}
    (K : Type*) [CommRing K] (r : RankArray n) :
    (X '' zeroCoordinates (zeroRegion r) : Set (CoordinateRing n K)) ⊆
      northwestGenerators K r := by
  rintro _ ⟨_, ⟨⟨i, j⟩, ⟨a, b, hab, hia, hjb⟩, rfl⟩, rfl⟩
  refine ⟨a, b, ?_⟩
  rw [hab]
  exact ⟨singletonEmbedding i, singletonEmbedding j, fun _ => hia, fun _ => hjb,
    (minor_singleton K i j).symm⟩

theorem mixedIdeal_zero_bound_reduction {n : ℕ} (K : Type*) [CommRing K]
    (r : RankArray n) (conditions : List (ℕ × ℕ)) :
    mixedIdeal K r conditions =
      mixedIdeal K (positiveBounds r) conditions ⊔ zeroVariableIdeal K (zeroRegion r) := by
  unfold mixedIdeal
  rw [northwestIdeal_zero_bound_reduction]
  change (northwestIdeal K (positiveBounds r) ⊔ zeroVariableIdeal K (zeroRegion r)) ⊔ _ =
    (northwestIdeal K (positiveBounds r) ⊔ _) ⊔ zeroVariableIdeal K (zeroRegion r)
  ac_rfl

theorem positive_northwest_generator_original_or_zero {n : ℕ}
    (K : Type*) [CommRing K] (r : RankArray n)
    {g : CoordinateRing n K} (hg : g ∈ northwestGenerators K (positiveBounds r)) :
    g ∈ northwestGenerators K r ∨ g ∈ zeroVariableIdeal K (zeroRegion r) := by
  obtain ⟨i, j, a, b, ha, hb, rfl⟩ := hg
  by_cases hr : r i j = 0
  · right
    apply minor_mem_zeroVariableIdeal K (zeroRegion_northwestClosed r) a b 0
    exact ⟨i, j, hr, ha 0, hb (Fin.rev 0)⟩
  · left
    have h : positiveBounds r i j = r i j := max_eq_left (Nat.one_le_iff_ne_zero.mpr hr)
    have hh : ∀ t (ht : t = r i j) (a b : Fin (t + 1) ↪o Fin n),
        (∀ p, a p ≤ i) → (∀ p, b p ≤ j) → minor K a b ∈ northwestGenerators K r := by
      rintro t rfl a b ha hb
      exact ⟨i, j, a, b, ha, hb, rfl⟩
    exact hh _ h a b ha hb

/-- Exact removal of all zero bounds in the mixed Gröbner assertion. -/
theorem mixedGroebner_of_positiveBounds {n : ℕ} (K : Type*) [CommRing K] [Nontrivial K]
    (r : RankArray n) (hr : ∀ i j, r i j = r j i) (conditions : List (ℕ × ℕ))
    (hpositive : (foldedOrder n).IsGroebnerBasis
      (mixedGenerators K (positiveBounds r) conditions)
      (mixedIdeal K (positiveBounds r) conditions)) :
    (foldedOrder n).IsGroebnerBasis (mixedGenerators K r conditions)
      (mixedIdeal K r conditions) := by
  classical
  let Z := zeroRegion r
  let V : Set (CoordinateRing n K) := X '' zeroCoordinates Z
  let J := zeroVariableIdeal K Z
  have hJ : J = Ideal.span V := zeroVariableIdeal_eq_span_image K Z
  have hV : (foldedOrder n).IsGroebnerBasis V J := by
    rw [hJ]
    exact MonomialOrder.isGroebnerBasis_variables (zeroCoordinates Z)
  have hext := hpositive.adjoin_variables
    (mixedGenerators_unit_leading K (positiveBounds r) conditions)
    (zeroCoordinates Z) (fun g hg hh => by
      rw [← zeroVariableIdeal_eq_span_image]
      exact mixedGenerators_ferrers_compatible K _ _ (zeroRegion_northwestClosed r)
        (zeroRegion_symmetric hr) g hg hh)
  have hext' : (foldedOrder n).IsGroebnerBasis
      (mixedGenerators K (positiveBounds r) conditions ∪ V) (mixedIdeal K r conditions) := by
    rw [mixedIdeal_zero_bound_reduction, zeroVariableIdeal_eq_span_image]
    exact hext
  apply (MonomialOrder.isGroebnerBasis_iff_forall_exists_degree_le_degree
    (mixedGenerators_unit_leading K r conditions)).mpr
  refine ⟨?_, ?_⟩
  · intro g hg
    rcases hg with hg | hg
    · exact (show northwestIdeal K r ≤ mixedIdeal K r conditions from le_sup_left)
        (Ideal.subset_span hg)
    · exact hext'.subset (Or.inl (Or.inr hg))
  · intro f hf hf0
    obtain ⟨g, hg, hg0, hgf⟩ := hext'.exists_degree_le_degree hf hf0
    have use_variable (hgJ : g ∈ J) :
        ∃ a ∈ mixedGenerators K r conditions,
          a ≠ 0 ∧ (foldedOrder n).degree a ≤ (foldedOrder n).degree f := by
      obtain ⟨a, ha, ha0, hag⟩ := hV.exists_degree_le_degree hgJ hg0
      exact ⟨a, Or.inl (zeroCoordinates_variables_subset_northwestGenerators K r ha),
        ha0, hag.trans hgf⟩
    rcases hg with (hg | hg) | hg
    · rcases positive_northwest_generator_original_or_zero K r hg with hg | hg
      · exact ⟨g, Or.inl hg, hg0, hgf⟩
      · exact use_variable hg
    · exact ⟨g, Or.inr hg, hg0, hgf⟩
    · exact ⟨g, Or.inl (zeroCoordinates_variables_subset_northwestGenerators K r hg), hg0, hgf⟩

end FourPapers.Symmetric

end
end


/- SOURCE HomogeneousDegreeCut.lean -/
section

set_option autoImplicit false

/-! # Adjoining a total-degree cutoff to a homogeneous ideal

For any monomial order, a homogeneous ideal and a power of the coordinate
ideal have compatible Gröbner bases.  The proof separates the homogeneous
component containing the leading monomial; it imposes no restriction on the
chosen monomial order.
-/

noncomputable section

namespace MonomialOrder

open MvPolynomial

variable {σ K : Type*} [Field K] (m : MonomialOrder σ)
variable {I : Ideal (MvPolynomial σ K)} {G H : Set (MvPolynomial σ K)}

attribute [local instance] MvPolynomial.gradedAlgebra

theorem homogeneousComponent_pow_idealOfVars_eq_zero {s d : ℕ}
    {f : MvPolynomial σ K} (hf : f ∈ idealOfVars σ K ^ s) (hds : d < s) :
    homogeneousComponent d f = 0 := by
  ext e
  change (homogeneousComponent d f).coeff e = (0 : K)
  rw [coeff_homogeneousComponent]
  split_ifs with he
  · exact (mem_pow_idealOfVars_iff' s f).mp hf e (he ▸ hds)
  · rfl

theorem degree_homogeneousComponent_degree (f : MvPolynomial σ K) :
    m.degree (homogeneousComponent ((m.degree f).degree) f) = m.degree f := by
  simpa only [homogeneousComponent, Finsupp.degree_eq_weight_one, Pi.one_def] using
    m.degree_weightedHomogeneousComponent_weight_degree (1 : σ → ℕ) f

theorem homogeneousComponent_degree_ne_zero {f : MvPolynomial σ K} (hf : f ≠ 0) :
    homogeneousComponent ((m.degree f).degree) f ≠ 0 := by
  intro hzero
  have hc := congrArg (fun p : MvPolynomial σ K => p.coeff (m.degree f)) hzero
  have hn := m.coeff_degree_ne_zero_iff.mpr hf
  exact hn (by simpa [coeff_homogeneousComponent] using hc)

/-- A Gröbner basis for a homogeneous ideal may be united with any Gröbner
basis of a power of the ideal of all coordinates. -/
theorem IsGroebnerBasis.adjoin_coordinate_power
    (hG : m.IsGroebnerBasis G I)
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    (s : ℕ) (hH : m.IsGroebnerBasis H (idealOfVars σ K ^ s)) :
    m.IsGroebnerBasis (G ∪ H) (I + idealOfVars σ K ^ s) := by
  classical
  have hunit : ∀ g ∈ G ∪ H, g ≠ 0 → IsUnit (m.leadingCoeff g) := by
    intro g hg hg0
    exact m.isUnit_leadingCoeff.mpr hg0
  apply (isGroebnerBasis_iff_forall_exists_degree_le_degree hunit).mpr
  refine ⟨?_, ?_⟩
  · intro g hg
    rcases hg with hg | hg
    · exact (show I ≤ I + idealOfVars σ K ^ s from le_sup_left) (hG.subset hg)
    · exact (show idealOfVars σ K ^ s ≤ I + idealOfVars σ K ^ s from le_sup_right) (hH.subset hg)
  · intro f hf hf0
    by_cases hlarge : s ≤ (m.degree f).degree
    · have hm : monomial (m.degree f) (1 : K) ∈ idealOfVars σ K ^ s :=
        (monomial_mem_pow_idealOfVars_iff s (m.degree f) one_ne_zero).mpr hlarge
      obtain ⟨g, hg, hg0, hgf⟩ := hH.exists_degree_le_degree hm
        (by simp)
      refine ⟨g, Or.inr hg, hg0, ?_⟩
      rw [m.degree_monomial, if_neg one_ne_zero] at hgf
      exact hgf
    · have hsmall : (m.degree f).degree < s := Nat.lt_of_not_ge hlarge
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hf
      have hcomp : homogeneousComponent ((m.degree f).degree) f ∈ I := by
        have hh := congrArg (homogeneousComponent ((m.degree f).degree)) hab
        rw [map_add, homogeneousComponent_pow_idealOfVars_eq_zero hb hsmall, add_zero] at hh
        exact hh ▸ homogeneousComponent_mem_of_mem hI ha _
      obtain ⟨g, hg, hg0, hgf⟩ := hG.exists_degree_le_degree hcomp
        (homogeneousComponent_degree_ne_zero m hf0)
      exact ⟨g, Or.inl hg, hg0, by simpa only [degree_homogeneousComponent_degree] using hgf⟩

theorem coordinate_power_isHomogeneous (s : ℕ) :
    (idealOfVars σ K ^ s).IsHomogeneous (homogeneousSubmodule σ K) := by
  have hvars : (idealOfVars σ K).IsHomogeneous (homogeneousSubmodule σ K) := by
    apply Ideal.homogeneous_span
    rintro _ ⟨i, rfl⟩
    exact ⟨1, isHomogeneous_X K i⟩
  induction s with
  | zero => simpa using (Ideal.IsHomogeneous.top (homogeneousSubmodule σ K))
  | succ s ih => simpa only [pow_succ] using ih.mul hvars

end MonomialOrder

end
end


/- SOURCE MixedDegreeCut.lean -/
section

set_option autoImplicit false

namespace FourPapers.Symmetric

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem mixedGenerators_homogeneous {n : ℕ} (K : Type*) [CommRing K]
    (r : RankArray n) (conditions : List (ℕ × ℕ)) :
    ∀ g ∈ mixedGenerators K r conditions, ∃ d, g.IsHomogeneous d := by
  rintro g (hg | hg)
  · obtain ⟨i, j, a, b, ha, hb, rfl⟩ := hg
    exact ⟨r i j + 1, minor_isHomogeneous_total K a b⟩
  · obtain ⟨ts, hts, k, δ, hsize, hscore, rfl⟩ := hg
    exact ⟨∑ j, (δ j).size, product_minors_isHomogeneous_total K δ⟩

theorem mixedIdeal_isHomogeneous_of_groebner {n : ℕ} (K : Type*) [Field K]
    (r : RankArray n) (conditions : List (ℕ × ℕ))
    (hG : (foldedOrder n).IsGroebnerBasis (mixedGenerators K r conditions)
      (mixedIdeal K r conditions)) :
    (mixedIdeal K r conditions).IsHomogeneous (homogeneousSubmodule (Entry n) K) := by
  rw [hG.ideal_eq_span]
  apply Ideal.homogeneous_span
  exact mixedGenerators_homogeneous K r conditions

theorem mixedGenerators_cons {n : ℕ} (K : Type*) [CommRing K]
    (r : RankArray n) (conditions : List (ℕ × ℕ)) (ts : ℕ × ℕ) :
    mixedGenerators K r (ts :: conditions) =
      mixedGenerators K r conditions ∪ symbolicGenerators K n ts.1 ts.2 := by
  ext f
  simp only [mixedGenerators, Set.mem_union, Set.mem_setOf_eq, List.mem_cons, exists_eq_or_imp]
  constructor
  · rintro (h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  · rintro ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

theorem mixedIdeal_cons {n : ℕ} (K : Type*) [CommRing K]
    (r : RankArray n) (conditions : List (ℕ × ℕ)) (ts : ℕ × ℕ) :
    mixedIdeal K r (ts :: conditions) =
      mixedIdeal K r conditions + symbolicPower (determinantalIdeal n K ts.1) ts.2 := by
  simp only [mixedIdeal, List.map_cons, List.sum_cons]
  ac_rfl

/-- Adjoining any size-one symbolic condition to an already established mixed
basis gives the exact new mixed basis, in every matrix dimension. -/
theorem mixedGroebner_cons_one {n : ℕ} (K : Type*) [Field K]
    (r : RankArray n) (conditions : List (ℕ × ℕ)) (s : ℕ)
    (hG : (foldedOrder n).IsGroebnerBasis (mixedGenerators K r conditions)
      (mixedIdeal K r conditions)) :
    (foldedOrder n).IsGroebnerBasis (mixedGenerators K r ((1, s) :: conditions))
      (mixedIdeal K r ((1, s) :: conditions)) := by
  rw [mixedGenerators_cons, mixedIdeal_cons]
  have hH := symbolicGenerators_one_groebner n K s
  rw [determinantalIdeal_one, symbolicPower_idealOfVars] at hH ⊢
  exact hG.adjoin_coordinate_power (foldedOrder n)
    (mixedIdeal_isHomogeneous_of_groebner K r conditions hG) s hH

end FourPapers.Symmetric

end


/- SOURCE CoefficientGenerators.lean -/
section
set_option autoImplicit false
noncomputable section
namespace FourPapers.Symmetric
open MvPolynomial
variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_minor (φ : R →+* S) {n t : ℕ} (a b : Fin t ↪o Fin n) :
    MvPolynomial.map φ (minor R a b) = minor S a b := by
  unfold minor
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [genericMatrix]

theorem map_northwestGenerators (φ : R →+* S) {n : ℕ} (r : RankArray n) :
    MvPolynomial.map φ '' northwestGenerators R r = northwestGenerators S r := by
  ext f
  constructor
  · rintro ⟨_, ⟨i, j, a, b, ha, hb, rfl⟩, rfl⟩
    exact ⟨i, j, a, b, ha, hb, map_minor φ a b⟩
  · rintro ⟨i, j, a, b, ha, hb, rfl⟩
    exact ⟨minor R a b, ⟨i, j, a, b, ha, hb, rfl⟩, map_minor φ a b⟩

theorem map_symbolicGenerators (φ : R →+* S) (n t s : ℕ) :
    MvPolynomial.map φ '' symbolicGenerators R n t s = symbolicGenerators S n t s := by
  ext f
  constructor
  · rintro ⟨_, ⟨k, δ, hsize, hscore, rfl⟩, rfl⟩
    refine ⟨k, δ, hsize, hscore, ?_⟩
    simp only [map_prod, MinorData.polynomial, map_minor]
  · rintro ⟨k, δ, hsize, hscore, rfl⟩
    refine ⟨∏ j, (δ j).polynomial R, ⟨k, δ, hsize, hscore, rfl⟩, ?_⟩
    simp only [map_prod, MinorData.polynomial, map_minor]

theorem map_mixedGenerators (φ : R →+* S) {n : ℕ} (r : RankArray n)
    (conditions : List (ℕ × ℕ)) :
    MvPolynomial.map φ '' mixedGenerators R r conditions = mixedGenerators S r conditions := by
  ext f
  constructor
  · rintro ⟨g, (hg | hg), rfl⟩
    · exact Or.inl (map_northwestGenerators φ r ▸ Set.mem_image_of_mem (MvPolynomial.map φ) hg)
    · obtain ⟨ts, hts, hg⟩ := hg
      exact Or.inr ⟨ts, hts,
        map_symbolicGenerators φ n ts.1 ts.2 ▸ Set.mem_image_of_mem (MvPolynomial.map φ) hg⟩
  · rintro (hf | ⟨ts, hts, hf⟩)
    · rw [← map_northwestGenerators φ r] at hf
      obtain ⟨g, hg, rfl⟩ := hf
      exact ⟨g, Or.inl hg, rfl⟩
    · rw [← map_symbolicGenerators φ n ts.1 ts.2] at hf
      obtain ⟨g, hg, rfl⟩ := hf
      exact ⟨g, Or.inr ⟨ts, hts, hg⟩, rfl⟩

theorem product_minors_leadingCoeff_mul_self {n k : ℕ} (R : Type*) [CommRing R]
    (δ : Fin k → MinorData n) :
    (foldedOrder n).leadingCoeff (∏ j, (δ j).polynomial R) *
      (foldedOrder n).leadingCoeff (∏ j, (δ j).polynomial R) = 1 := by
  classical
  rw [(foldedOrder n).leadingCoeff_prod_of_regular
    (fun j _ => ((δ j).leadingCoeff_polynomial_isUnit R).isRegular)]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro j hj
  rw [MinorData.leadingCoeff_polynomial]
  exact signCoefficient_mul_self R _

theorem mixedGenerators_leadingCoeff_mul_self {n : ℕ} (R : Type*) [CommRing R]
    (r : RankArray n) (conditions : List (ℕ × ℕ)) :
    ∀ g ∈ mixedGenerators R r conditions,
      (foldedOrder n).leadingCoeff g * (foldedOrder n).leadingCoeff g = 1 := by
  rintro g (hg | hg)
  · obtain ⟨i, j, a, b, ha, hb, rfl⟩ := hg
    rw [minor_leadingCoeff]
    exact signCoefficient_mul_self R _
  · obtain ⟨ts, hts, k, δ, hsize, hscore, rfl⟩ := hg
    exact product_minors_leadingCoeff_mul_self R δ

end FourPapers.Symmetric

end
end


/- SOURCE LeadingSignNormalization.lean -/
section
set_option autoImplicit false
noncomputable section
namespace MonomialOrder
open MvPolynomial
variable {σ R : Type*} [CommRing R] [Nontrivial R] {m : MonomialOrder σ}
  {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}

/-- Multiplying a generator by its involutive leading coefficient makes it
monic, while preserving both its leading exponent and its ideal. -/
theorem IsGroebnerBasis.normalize_involutive_leading
    (hG : m.IsGroebnerBasis G I)
    (hsign : ∀ g ∈ G, m.leadingCoeff g * m.leadingCoeff g = 1) :
    m.IsGroebnerBasis ((fun f => C (m.leadingCoeff f) * f) '' G) I ∧
      ∀ g ∈ ((fun f => C (m.leadingCoeff f) * f) '' G), m.leadingCoeff g = 1 := by
  classical
  have hu : ∀ g ∈ G, IsUnit (m.leadingCoeff g) := by
    intro g hg
    exact IsUnit.of_mul_eq_one _ (hsign g hg)
  have hdeg : ∀ g ∈ G, m.degree (C (m.leadingCoeff g) * g) = m.degree g := by
    intro g hg
    rw [← smul_eq_C_mul, m.degree_smul_of_isRegular (hu g hg).isRegular]
  have hlc : ∀ g ∈ G, m.leadingCoeff (C (m.leadingCoeff g) * g) = 1 := by
    intro g hg
    rw [m.leadingCoeff_mul_of_isRegular_left]
    · rw [m.leadingCoeff_C]
      exact hsign g hg
    · simpa only [m.leadingCoeff_C] using (hu g hg).isRegular
  have hnz : ∀ g ∈ G, C (m.leadingCoeff g) * g ≠ 0 := by
    intro g hg
    apply m.leadingCoeff_ne_zero_iff.mp
    rw [hlc g hg]
    exact one_ne_zero
  refine ⟨?_, ?_⟩
  · apply (isGroebnerBasis_iff_forall_exists_degree_le_degree
      (fun g hg _ => ?_)).mpr
    · refine ⟨?_, ?_⟩
      · rintro _ ⟨g, hg, rfl⟩
        exact I.mul_mem_left _ (hG.subset hg)
      · intro f hf hf0
        obtain ⟨g, hg, hg0, hgf⟩ := hG.exists_degree_le_degree hf hf0
        exact ⟨C (m.leadingCoeff g) * g, ⟨g, hg, rfl⟩, hnz g hg,
          (hdeg g hg).trans_le hgf⟩
    · obtain ⟨g, hg, rfl⟩ := hg
      rw [hlc g hg]
      exact isUnit_one
  · rintro _ ⟨g, hg, rfl⟩
    exact hlc g hg

end MonomialOrder

end
end


/- SOURCE UniversalStandardBasis.lean -/
section
set_option autoImplicit false
noncomputable section
namespace MonomialOrder
open MvPolynomial
variable {σ R S : Type*} [CommRing R] [CommRing S] {m : MonomialOrder σ}
  {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}

/-- The same standard exponents give a quotient basis after every coefficient
map, including nonflat maps and maps to the zero ring. -/
theorem IsGroebnerBasis.fixed_standard_basis_after_basechange
    (hG : m.IsGroebnerBasis G I) (φ : R →+* S)
    (hunit : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    let J := I.map (MvPolynomial.map φ)
    let b : m.standardMonomials I → MvPolynomial σ S ⧸ J :=
      fun c => Ideal.Quotient.mk J (monomial c.val 1)
    LinearIndependent S b ∧ Submodule.span S (Set.range b) = ⊤ := by
  classical
  dsimp only
  rcases subsingleton_or_nontrivial S with hS | hS
  · letI := hS
    refine ⟨linearIndependent_of_subsingleton, ?_⟩
    apply top_unique
    intro x hx
    rw [Subsingleton.elim x 0]
    exact Submodule.zero_mem _
  · letI := hS
    let J := I.map (MvPolynomial.map φ)
    have hmap := hG.map_of_unit_leading φ hunit
    have hunit' : ∀ g ∈ MvPolynomial.map φ '' G,
        g ≠ 0 → IsUnit (m.leadingCoeff g) := by
      rintro _ ⟨g, hg, rfl⟩ hg0
      have hg0' : g ≠ 0 := fun hz => hg0 (by simp [hz])
      have hn : φ (m.leadingCoeff g) ≠ 0 := ((hunit g hg hg0').map φ).ne_zero
      rw [m.leadingCoeff_map_of_leadingCoeff_ne_zero φ hn]
      exact (hunit g hg hg0').map φ
    have hstd : m.standardMonomials J = m.standardMonomials I :=
      hG.standardMonomials_map_of_unit_leading φ hunit
    let e : m.standardMonomials I ≃ m.standardMonomials J :=
      { toFun := fun c => ⟨c.val, by rw [hstd]; exact c.property⟩
        invFun := fun c => ⟨c.val, by rw [← hstd]; exact c.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let B := hmap.basisQuotient hunit'
    have hfun : (fun c : m.standardMonomials I =>
        Ideal.Quotient.mk J (monomial c.val (1 : S))) = fun c => B (e c) := by
      funext c
      exact (hmap.basisQuotient_apply hunit' (e c)).symm
    change LinearIndependent S (fun c : m.standardMonomials I =>
      Ideal.Quotient.mk J (monomial c.val 1)) ∧
      Submodule.span S (Set.range (fun c : m.standardMonomials I =>
        Ideal.Quotient.mk J (monomial c.val 1))) = ⊤
    rw [hfun]
    refine ⟨B.linearIndependent.comp e e.injective, ?_⟩
    have hrange : Set.range (fun c => B (e c)) = Set.range B := by
      ext x
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨e c, rfl⟩
      · rintro ⟨d, rfl⟩
        obtain ⟨c, rfl⟩ := e.surjective d
        exact ⟨c, rfl⟩
    rw [hrange]
    exact B.span_eq

end MonomialOrder

end
end


/- SOURCE remote_IntegralStatements.lean -/
section
namespace FourPapers.Symmetric
universe v
open MvPolynomial
/-- Exact allowed range for each symbolic threshold in Theorem 1.2. -/
def ValidSymbolicConditions (n : ℕ) (conditions : List (ℕ × ℕ)) : Prop :=
  ∀ ts ∈ conditions, 1 ≤ ts.1 ∧ ts.1 ≤ n ∧ 1 ≤ ts.2

/-- The field assertion of Theorem 1.2. `mixedIdeal` uses the true symbolic powers
as defined by localization and proved equivalent to that definition for prime ideals.
The proposed product generators occur only in `mixedGenerators`. -/
def CompatibleGroebnerAssertion : Prop :=
  ∀ (n : ℕ) (K : Type v) [Field K] (r : RankArray n),
    (∀ i j, r i j = r j i) →
    ∀ conditions : List (ℕ × ℕ), ValidSymbolicConditions n conditions →
      (foldedOrder n).IsGroebnerBasis (mixedGenerators K r conditions)
        (mixedIdeal K r conditions)

/-- Integral sign normalization, which is multiplication by the leading sign. -/
def normalizedMixedGenerators {n : ℕ} (r : RankArray n)
    (conditions : List (ℕ × ℕ)) : Set (CoordinateRing n ℤ) :=
  (fun f => C ((foldedOrder n).leadingCoeff f) * f) '' mixedGenerators ℤ r conditions

/-- The integral model over a general coefficient ring is defined by base change
of the displayed integral generators, exactly as in Theorem 1.2. -/
def integralMixedIdeal {n : ℕ} (K : Type v) [CommRing K] (r : RankArray n)
    (conditions : List (ℕ × ℕ)) : Ideal (CoordinateRing n K) :=
  Ideal.span ((MvPolynomial.map (Int.castRingHom K)) '' normalizedMixedGenerators r conditions)

/-- Standard exponents of the proposed monic integral generating family. -/
def MixedStandardExponents {n : ℕ} (r : RankArray n) (conditions : List (ℕ × ℕ)) :=
  {e : Entry n →₀ ℕ // monomial e (1 : ℤ) ∉
    northwestAntidiagonalIdeal ℤ r ⊔
      ∑ ts ∈ conditions.toFinset, symbolicAntidiagonalIdeal ℤ n ts.1 ts.2}

/-- The quotient basis assertion under every commutative base change, expressed
as independence and spanning of the specified monomial residue classes. -/
def IntegralBaseChangeAssertion : Prop :=
  ∀ (n : ℕ) (r : RankArray n), (∀ i j, r i j = r j i) →
    ∀ conditions : List (ℕ × ℕ), ValidSymbolicConditions n conditions →
      (foldedOrder n).IsGroebnerBasis (normalizedMixedGenerators r conditions)
        (Ideal.span (normalizedMixedGenerators r conditions)) ∧
      (∀ g ∈ normalizedMixedGenerators r conditions,
        (foldedOrder n).leadingCoeff g = 1) ∧
      ∀ (K : Type v) [CommRing K],
        let I := integralMixedIdeal K r conditions
        let b : MixedStandardExponents r conditions → CoordinateRing n K ⧸ I :=
          fun e => Ideal.Quotient.mk I (monomial e.val 1)
        LinearIndependent K b ∧ Submodule.span K (Set.range b) = ⊤

end FourPapers.Symmetric
end


/- SOURCE IntegralBaseChangeTheorem.lean -/
section

set_option autoImplicit false
noncomputable section

namespace FourPapers.Symmetric
open MvPolynomial
universe v

def mixedAntidiagonals {n : ℕ} (R : Type*) [CommRing R] (r : RankArray n)
    (conditions : List (ℕ × ℕ)) : Set (CoordinateRing n R) :=
  northwestAntidiagonals R r ∪
    {f | ∃ ts ∈ conditions, f ∈ symbolicAntidiagonals R n ts.1 ts.2}

theorem mixedAntidiagonal_span {n : ℕ} (R : Type*) [CommRing R] (r : RankArray n)
    (conditions : List (ℕ × ℕ)) :
    Ideal.span (mixedAntidiagonals R r conditions) =
      northwestAntidiagonalIdeal R r ⊔
        ∑ ts ∈ conditions.toFinset, symbolicAntidiagonalIdeal R n ts.1 ts.2 := by
  classical
  rw [Ideal.sum_eq_sup, Finset.sup_eq_iSup]
  unfold mixedAntidiagonals northwestAntidiagonalIdeal symbolicAntidiagonalIdeal
  rw [Ideal.span_union]
  congr 1
  simp only [← Ideal.span_iUnion]
  congr 1
  ext f
  simp

theorem monomial_degrees_mixedGenerators {n : ℕ} (R : Type*) [CommRing R] [Nontrivial R]
    (r : RankArray n) (conditions : List (ℕ × ℕ)) :
    (fun g => monomial ((foldedOrder n).degree g) (1 : R)) '' mixedGenerators R r conditions =
      mixedAntidiagonals R r conditions := by
  ext f
  constructor
  · rintro ⟨g, (hg | hg), rfl⟩
    · obtain ⟨i, j, a, b, ha, hb, rfl⟩ := hg
      exact Or.inl ⟨i, j, a, b, ha, hb, by simpa only [minor_degree, antidiagonal]⟩
    · obtain ⟨ts, hts, k, δ, hsize, hscore, rfl⟩ := hg
      exact Or.inr ⟨ts, hts, k, δ, hsize, hscore, by simpa only [product_minors_degree]⟩
  · rintro (hf | ⟨ts, hts, hf⟩)
    · obtain ⟨i, j, a, b, ha, hb, rfl⟩ := hf
      exact ⟨minor R a b, Or.inl ⟨i, j, a, b, ha, hb, rfl⟩,
        by simpa only [minor_degree, antidiagonal]⟩
    · obtain ⟨k, δ, hsize, hscore, rfl⟩ := hf
      exact ⟨∏ j, (δ j).polynomial R,
        Or.inr ⟨ts, hts, k, δ, hsize, hscore, rfl⟩,
        by simpa only [product_minors_degree]⟩

theorem mixedGenerators_nonzero {n : ℕ} (R : Type*) [CommRing R] [Nontrivial R]
    (r : RankArray n) (conditions : List (ℕ × ℕ)) :
    ∀ g ∈ mixedGenerators R r conditions, g ≠ 0 := by
  intro g hg
  apply (foldedOrder n).leadingCoeff_ne_zero_iff.mp
  exact (IsUnit.of_mul_eq_one _ (mixedGenerators_leadingCoeff_mul_self R r conditions g hg)).ne_zero

theorem mixed_standardMonomials_eq {n : ℕ} (R : Type*) [CommRing R] [Nontrivial R]
    (r : RankArray n) (conditions : List (ℕ × ℕ))
    {I : Ideal (CoordinateRing n R)}
    (hG : (foldedOrder n).IsGroebnerBasis (mixedGenerators R r conditions) I) :
    (foldedOrder n).standardMonomials I =
      {e | monomial e (1 : R) ∉ northwestAntidiagonalIdeal R r ⊔
        ∑ ts ∈ conditions.toFinset, symbolicAntidiagonalIdeal R n ts.1 ts.2} := by
  classical
  have hJ : northwestAntidiagonalIdeal R r ⊔
      ∑ ts ∈ conditions.toFinset, symbolicAntidiagonalIdeal R n ts.1 ts.2 =
      Ideal.span ((fun d => monomial d (1 : R)) ''
        ((foldedOrder n).degree '' mixedGenerators R r conditions)) := by
    rw [← mixedAntidiagonal_span, Set.image_image, monomial_degrees_mixedGenerators]
  ext e
  rw [hG.mem_standardMonomials_iff]
  change (∀ g ∈ mixedGenerators R r conditions, g ≠ 0 →
    ¬ (foldedOrder n).degree g ≤ e) ↔ _
  rw [hJ]
  have hm : monomial e (1 : R) ∈
      Ideal.span ((fun d => monomial d (1 : R)) ''
        ((foldedOrder n).degree '' mixedGenerators R r conditions)) ↔
      ∃ g ∈ mixedGenerators R r conditions, (foldedOrder n).degree g ≤ e := by
    rw [mem_ideal_span_monomial_image]
    simp
  simp only [Set.mem_setOf_eq]
  rw [hm]
  constructor
  · rintro h ⟨g, hg, hge⟩
    exact h g hg (mixedGenerators_nonzero R r conditions g hg) hge
  · intro h g hg hg0 hge
    exact h ⟨g, hg, hge⟩

theorem integral_mixedGroebner_of_rational {n : ℕ} (r : RankArray n)
    (conditions : List (ℕ × ℕ))
    (hQ : (foldedOrder n).IsGroebnerBasis (mixedGenerators ℚ r conditions)
      (mixedIdeal ℚ r conditions)) :
    (foldedOrder n).IsGroebnerBasis (mixedGenerators ℤ r conditions)
      (Ideal.span (mixedGenerators ℤ r conditions)) := by
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  apply (MonomialOrder.isGroebnerBasis_map_iff hinj
    (mixedGenerators_unit_leading ℤ r conditions) Ideal.subset_span).mp
  rw [Ideal.map_span, map_mixedGenerators]
  simpa only [hQ.ideal_eq_span] using hQ

/-- The complete integral and arbitrary-base-change clause follows from the
rational mixed Gröbner assertion for exactly the same parameters. -/
theorem integralBaseChange_of_rational {n : ℕ} (r : RankArray n)
    (conditions : List (ℕ × ℕ))
    (hQ : (foldedOrder n).IsGroebnerBasis (mixedGenerators ℚ r conditions)
      (mixedIdeal ℚ r conditions)) :
    (foldedOrder n).IsGroebnerBasis (normalizedMixedGenerators r conditions)
        (Ideal.span (normalizedMixedGenerators r conditions)) ∧
      (∀ g ∈ normalizedMixedGenerators r conditions, (foldedOrder n).leadingCoeff g = 1) ∧
      ∀ (K : Type v) [CommRing K],
        let I := integralMixedIdeal K r conditions
        let b : MixedStandardExponents r conditions → CoordinateRing n K ⧸ I :=
          fun e => Ideal.Quotient.mk I (monomial e.val 1)
        LinearIndependent K b ∧ Submodule.span K (Set.range b) = ⊤ := by
  have hZ := integral_mixedGroebner_of_rational r conditions hQ
  obtain ⟨hN, hmonic⟩ := hZ.normalize_involutive_leading
    (mixedGenerators_leadingCoeff_mul_self ℤ r conditions)
  change (foldedOrder n).IsGroebnerBasis (normalizedMixedGenerators r conditions)
    (Ideal.span (mixedGenerators ℤ r conditions)) at hN
  have hspan : Ideal.span (mixedGenerators ℤ r conditions) =
      Ideal.span (normalizedMixedGenerators r conditions) := hN.ideal_eq_span
  have hN' : (foldedOrder n).IsGroebnerBasis (normalizedMixedGenerators r conditions)
      (Ideal.span (normalizedMixedGenerators r conditions)) := hspan ▸ hN
  refine ⟨hN', hmonic, ?_⟩
  intro K _
  have hunit : ∀ g ∈ normalizedMixedGenerators r conditions,
      g ≠ 0 → IsUnit ((foldedOrder n).leadingCoeff g) := by
    intro g hg hg0
    rw [hmonic g hg]
    exact isUnit_one
  have hb := hN'.fixed_standard_basis_after_basechange (Int.castRingHom K) hunit
  have hstd := mixed_standardMonomials_eq ℤ r conditions hZ
  rw [hspan] at hstd
  dsimp only at hb
  rw [Ideal.map_span, hstd] at hb
  exact hb

theorem integralBaseChangeAssertion_of_compatible
    (h : CompatibleGroebnerAssertion.{0}) : IntegralBaseChangeAssertion.{v} := by
  intro n r hr conditions hc
  exact integralBaseChange_of_rational r conditions (h n ℚ r hr conditions hc)

end FourPapers.Symmetric

end
end


/- SOURCE SymbolicPowerFunctorial.lean -/
section

set_option autoImplicit false

/-! # Functoriality of genuine symbolic powers

These lemmas concern the denominator definition already identified with
localization at the prime.  The witnesses are cleared explicitly in both
directions.
-/

noncomputable section

namespace FourPapers.Symmetric

variable {R S : Type*} [CommRing R] [CommRing S]

@[simp] theorem symbolicPower_zero (P : Ideal R) [P.IsPrime] :
    symbolicPower P 0 = ⊤ := by
  apply top_unique
  simpa using pow_le_symbolicPower P 0

@[simp] theorem symbolicPower_one (P : Ideal R) [P.IsPrime] :
    symbolicPower P 1 = P := by
  apply le_antisymm
  · intro f hf
    obtain ⟨g, hg, hgf⟩ := (mem_symbolicPower_iff P 1 f).mp hf
    exact ((inferInstance : P.IsPrime).mem_or_mem (by simpa using hgf)).resolve_left hg
  · simpa using pow_le_symbolicPower P 1

theorem symbolicPower_antitone (P : Ideal R) [P.IsPrime] {a b : ℕ} (hab : a ≤ b) :
    symbolicPower P b ≤ symbolicPower P a := by
  intro f hf
  obtain ⟨g, hg, hgf⟩ := (mem_symbolicPower_iff P b f).mp hf
  exact (mem_symbolicPower_iff P a f).mpr
    ⟨g, hg, Ideal.pow_le_pow_right hab hgf⟩

theorem mul_mem_symbolicPower_add (P : Ideal R) [P.IsPrime]
    {a b : ℕ} {f g : R} (hf : f ∈ symbolicPower P a)
    (hg : g ∈ symbolicPower P b) : f * g ∈ symbolicPower P (a + b) := by
  obtain ⟨c, hc, hcf⟩ := (mem_symbolicPower_iff P a f).mp hf
  obtain ⟨d, hd, hdg⟩ := (mem_symbolicPower_iff P b g).mp hg
  apply (mem_symbolicPower_iff P (a + b) (f * g)).mpr
  refine ⟨c * d, P.primeCompl.mul_mem hc hd, ?_⟩
  rw [pow_add]
  convert Ideal.mul_mem_mul hcf hdg using 1 <;> ring

theorem prod_mem_symbolicPower_sum {ι : Type*} (P : Ideal R) [P.IsPrime]
    (s : Finset ι) (a : ι → ℕ) (f : ι → R)
    (hf : ∀ i ∈ s, f i ∈ symbolicPower P (a i)) :
    ∏ i ∈ s, f i ∈ symbolicPower P (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    exact mul_mem_symbolicPower_add P (hf i (by simp))
      (ih (fun j hj => hf j (by simp [hj])))

theorem map_symbolicPower_le_of_comap (φ : R →+* S) (P : Ideal R) (Q : Ideal S)
    [P.IsPrime] [Q.IsPrime] (hPQ : Q.comap φ = P)
    (hmap : P.map φ ≤ Q) (s : ℕ) :
    (symbolicPower P s).map φ ≤ symbolicPower Q s := by
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  obtain ⟨g, hg, hgf⟩ := (mem_symbolicPower_iff P s f).mp hf
  apply (mem_symbolicPower_iff Q s (φ f)).mpr
  refine ⟨φ g, ?_, ?_⟩
  · intro h
    exact hg (hPQ ▸ h)
  · have hm := Ideal.mem_map_of_mem φ hgf
    rw [Ideal.map_pow] at hm
    exact Ideal.pow_right_mono hmap s (by simpa only [map_mul] using hm)

theorem symbolicPower_map_equiv (e : R ≃+* S) (P : Ideal R) [P.IsPrime] (s : ℕ) :
    (symbolicPower P s).map e.toRingHom = symbolicPower (P.map e.toRingHom) s := by
  have hcontract := Ideal.comap_map_of_bijective e.toRingHom e.bijective (I := P)
  have hprime : (P.map e.toRingHom).IsPrime := by
    have he : P.map e.toRingHom = P.comap e.symm.toRingHom := by
      ext y
      rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
      · intro hy
        exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
    rw [he]
    exact Ideal.comap_isPrime _ _
  letI := hprime
  apply le_antisymm
  · exact map_symbolicPower_le_of_comap e.toRingHom P (P.map e.toRingHom)
      hcontract le_rfl s
  · intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨z, hz, hzx⟩ := (mem_symbolicPower_iff (P.map e.toRingHom) s (e x)).mp hy
    apply Ideal.mem_map_of_mem
    apply (mem_symbolicPower_iff P s x).mpr
    refine ⟨e.symm z, ?_, ?_⟩
    · intro h
      apply hz
      simpa using Ideal.mem_map_of_mem e.toRingHom h
    · have : z * e x ∈ (P ^ s).map e.toRingHom := by
        simpa only [Ideal.map_pow] using hzx
      rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective] at this
      obtain ⟨a, ha, hea⟩ := this
      have : a = e.symm z * x := by
        apply e.injective
        change e a = z * e x at hea
        rw [map_mul, e.apply_symm_apply]
        exact hea
      exact this ▸ ha

section Localization

variable (M : Submonoid R) [Algebra R S] [IsLocalization M S]
variable (P : Ideal R) [P.IsPrime]
variable (hM : Disjoint (M : Set R) (P : Set R))

include M hM in
theorem symbolicPower_comap_localization (s : ℕ) :
    (symbolicPower (P.map (algebraMap R S)) s).comap (algebraMap R S) =
      symbolicPower P s := by
  let Q := P.map (algebraMap R S)
  letI : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M S P inferInstance hM
  have hcontract : Q.comap (algebraMap R S) = P :=
    IsLocalization.under_map_of_isPrime_disjoint M S inferInstance hM
  apply le_antisymm
  · intro f hf
    obtain ⟨b, hb, hbf⟩ := (mem_symbolicPower_iff Q s (algebraMap R S f)).mp hf
    obtain ⟨a, t, hat⟩ := IsLocalization.exists_mk'_eq M b
    have ha : a ∉ P := by
      intro ha
      apply hb
      rw [← hat, IsLocalization.mk'_mem_iff]
      exact Ideal.mem_map_of_mem _ ha
    have haf : algebraMap R S (a * f) ∈ (P ^ s).map (algebraMap R S) := by
      have h := (Q ^ s).mul_mem_left (algebraMap R S (t : R)) hbf
      rw [← hat] at h
      have ht : algebraMap R S (t : R) * IsLocalization.mk' S a t =
          algebraMap R S a := IsLocalization.mk'_spec' S a t
      rw [← mul_assoc, ht, ← map_mul] at h
      simpa only [Ideal.map_pow] using h
    obtain ⟨u, hu, huf⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff M S (P ^ s) (a * f)).mp haf
    apply (mem_symbolicPower_iff P s f).mpr
    refine ⟨u * a, P.primeCompl.mul_mem ?_ ha, ?_⟩
    · exact Set.disjoint_left.mp hM hu
    · simpa only [mul_assoc] using huf
  · exact (Ideal.map_le_iff_le_comap).mp
      (map_symbolicPower_le_of_comap (algebraMap R S) P Q hcontract le_rfl s)

include M hM in
theorem symbolicPower_map_localization (s : ℕ) :
    (symbolicPower P s).map (algebraMap R S) =
      symbolicPower (P.map (algebraMap R S)) s := by
  rw [← symbolicPower_comap_localization (S := S) M P hM s]
  exact IsLocalization.map_under M S _

end Localization

end FourPapers.Symmetric

end
end


/- SOURCE SymbolicChartTransport.lean -/
section

set_option autoImplicit false

/-! # Symbolic powers in an actual localization chart

A chart is a ring equivalence, followed by an actual localization, followed
by a ring equivalence.  If its image prime is proper, the localized
denominators automatically avoid the original prime.  Both image and
contraction of every symbolic power are then exact.  No determinantal
symbolic-power formula is assumed.
-/

noncomputable section

namespace FourPapers.Symmetric

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]

theorem ideal_isPrime_map_ringEquiv (e : R ≃+* A) (P : Ideal R) [P.IsPrime] :
    (P.map e.toRingHom).IsPrime := by
  have he : P.map e.toRingHom = P.comap e.symm.toRingHom := by
    ext y
    rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
  rw [he]
  exact Ideal.comap_isPrime _ _

section

variable (M : Submonoid A) [Algebra A B] [IsLocalization M B]
variable (e : R ≃+* A) (d : B ≃+* C)
variable (P : Ideal R) [P.IsPrime] (Q : Ideal C) [Q.IsPrime]
variable (hPQ : ((P.map e.toRingHom).map (algebraMap A B)).map d.toRingHom = Q)

include d Q hPQ in
theorem symbolicChart_denominators_disjoint :
    Disjoint (M : Set A) (P.map e.toRingHom : Set A) := by
  apply (IsLocalization.map_algebraMap_ne_top_iff_disjoint M B
    (P.map e.toRingHom)).mp
  intro htop
  have : Q = ⊤ := by rw [← hPQ, htop, Ideal.map_top]
  exact (inferInstance : Q.IsPrime).ne_top this

include M hPQ in
/-- Exact image of a symbolic power under the chart. -/
theorem symbolicPower_map_chart (s : ℕ) :
    (((symbolicPower P s).map e.toRingHom).map (algebraMap A B)).map d.toRingHom =
      symbolicPower Q s := by
  let P' := P.map e.toRingHom
  letI : P'.IsPrime := ideal_isPrime_map_ringEquiv e P
  have hM := symbolicChart_denominators_disjoint M e d P Q hPQ
  letI : (P'.map (algebraMap A B)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M B P' inferInstance hM
  rw [symbolicPower_map_equiv, symbolicPower_map_localization (S := B) M P' hM,
    symbolicPower_map_equiv, hPQ]

include M hPQ in
/-- Exact contraction under the same chart, including arbitrary exponents. -/
theorem symbolicPower_comap_chart (s : ℕ) :
    (((symbolicPower Q s).comap d.toRingHom).comap
      (algebraMap A B)).comap e.toRingHom = symbolicPower P s := by
  let P' := P.map e.toRingHom
  letI : P'.IsPrime := ideal_isPrime_map_ringEquiv e P
  have hM := symbolicChart_denominators_disjoint M e d P Q hPQ
  letI : (P'.map (algebraMap A B)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M B P' inferInstance hM
  have hd : (symbolicPower Q s).comap d.toRingHom =
      symbolicPower (P'.map (algebraMap A B)) s := by
    rw [← hPQ, ← symbolicPower_map_equiv d]
    exact Ideal.comap_map_of_bijective d.toRingHom d.bijective
  rw [hd, symbolicPower_comap_localization (S := B) M P' hM s,
    ← symbolicPower_map_equiv e]
  exact Ideal.comap_map_of_bijective e.toRingHom e.bijective

end

end FourPapers.Symmetric

end
end


/- SOURCE GenericSymbolicCoefficientExtension.lean -/
section

set_option autoImplicit false

/-! # Symbolic coefficient extension from exact field presentations

This is an induction lemma, not an assumed symbolic-power formula.  Given
the already proved Gröbner presentations over the original field and the
fraction field of the new coefficient domain, unit-leading-coefficient
division proves the corresponding presentation over that domain.  Symbolic
denominators are preserved by the exact contractions of the prime ideals.
-/

noncomputable section

namespace FourPapers.Symmetric

open MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S] [IsDomain S]

theorem symbolicPower_map_coeff_of_fraction_groebner
    (m : MonomialOrder σ) (φ : R →+* S) (hφ : Function.Injective φ)
    (P : Ideal (MvPolynomial σ R)) [P.IsPrime] (s : ℕ)
    (G : Set (MvPolynomial σ R))
    (hG : m.IsGroebnerBasis G (symbolicPower P s))
    (hunit : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g))
    (hQprime : (P.map (MvPolynomial.map φ)).IsPrime)
    (hQcontract : (P.map (MvPolynomial.map φ)).comap (MvPolynomial.map φ) = P)
    (hZprime : ((P.map (MvPolynomial.map φ)).map
      (MvPolynomial.map (algebraMap S (FractionRing S)))).IsPrime)
    (hZcontract : ((P.map (MvPolynomial.map φ)).map
      (MvPolynomial.map (algebraMap S (FractionRing S)))).comap
      (MvPolynomial.map (algebraMap S (FractionRing S))) = P.map (MvPolynomial.map φ))
    (hGF : m.IsGroebnerBasis
      (MvPolynomial.map (algebraMap S (FractionRing S)) '' (MvPolynomial.map φ '' G))
      (symbolicPower ((P.map (MvPolynomial.map φ)).map
        (MvPolynomial.map (algebraMap S (FractionRing S)))) s)) :
    (symbolicPower P s).map (MvPolynomial.map φ) =
      symbolicPower (P.map (MvPolynomial.map φ)) s := by
  let ψ := algebraMap S (FractionRing S)
  have hψ : Function.Injective ψ := IsFractionRing.injective S (FractionRing S)
  let Q := P.map (MvPolynomial.map φ)
  let Z := Q.map (MvPolynomial.map ψ)
  letI : Q.IsPrime := hQprime
  letI : Z.IsPrime := hZprime
  let J := (symbolicPower P s).map (MvPolynomial.map φ)
  have hJG : m.IsGroebnerBasis (MvPolynomial.map φ '' G) J :=
    hG.map hφ hunit
  have hJUnit : ∀ g ∈ MvPolynomial.map φ '' G,
      g ≠ 0 → IsUnit (m.leadingCoeff g) := by
    rintro _ ⟨g, hg, rfl⟩ hg0
    rw [m.leadingCoeff_map_of_injective hφ]
    exact (hunit g hg (fun h => hg0 (by simp [h]))).map φ
  have hJF : J.map (MvPolynomial.map ψ) = symbolicPower Z s := by
    rw [hJG.ideal_eq_span, Ideal.map_span]
    exact hGF.ideal_eq_span.symm
  have hJcontract : (J.map (MvPolynomial.map ψ)).comap (MvPolynomial.map ψ) = J :=
    hJG.comap_map_eq hψ hJUnit
  apply le_antisymm
  · exact map_symbolicPower_le_of_comap (MvPolynomial.map φ) P Q
      hQcontract le_rfl s
  · intro f hf
    have hfZ : MvPolynomial.map ψ f ∈ symbolicPower Z s :=
      map_symbolicPower_le_of_comap (MvPolynomial.map ψ) Q Z
        hZcontract le_rfl s (Ideal.mem_map_of_mem _ hf)
    rw [← hJF] at hfZ
    change f ∈ J
    rw [← hJcontract]
    exact hfZ


end FourPapers.Symmetric

end
end


/- SOURCE InitialIdealComparison.lean -/
section
set_option autoImplicit false
namespace MonomialOrder
open MvPolynomial
theorem ideal_eq_of_le_of_initial_le {σ R : Type*} [CommRing R]
    (m : MonomialOrder σ) {J K : Ideal (MvPolynomial σ R)} (hJK : J ≤ K)
    (hinit : Ideal.span (m.leadingTerm '' (K : Set (MvPolynomial σ R))) ≤
      Ideal.span (m.leadingTerm '' (J : Set (MvPolynomial σ R)))) : K = J := by
  have h : m.IsGroebnerBasis (J : Set (MvPolynomial σ R)) K :=
    ⟨hJK, le_antisymm hinit (Ideal.span_mono (Set.image_mono hJK))⟩
  simpa using h.ideal_eq_span
end MonomialOrder

end

#print axioms FourPapers.Symmetric.symbolicGenerators_one_groebner
#print axioms FourPapers.Symmetric.mixedGroebner_of_positiveBounds
#print axioms FourPapers.Symmetric.mixedGroebner_cons_one
#print axioms FourPapers.Symmetric.integralBaseChangeAssertion_of_compatible
#print axioms FourPapers.Symmetric.symbolicPower_map_coeff_of_fraction_groebner
#print axioms FourPapers.Symmetric.symbolicPower_comap_chart
#print axioms MonomialOrder.ideal_eq_of_le_of_initial_le

/- SOURCE MixedReductionTheorem.lean -/
section

set_option autoImplicit false

namespace FourPapers.Symmetric.Reduction
open MvPolynomial

universe v

/-- The one remaining positive-rank, positive-threshold field assertion.
This declaration is a proposition, not an asserted theorem. -/
def PositiveCoreAssertion : Prop :=
  ∀ (n : ℕ) (K : Type v) [Field K] (r : RankArray n),
    (∀ i j, r i j = r j i) →
    (∀ i j, 1 ≤ r i j) →
    ∀ conditions : List (ℕ × ℕ), ValidSymbolicConditions n conditions →
      (∀ ts ∈ conditions, 2 ≤ ts.1) →
      (foldedOrder n).IsGroebnerBasis (mixedGenerators K r conditions)
        (mixedIdeal K r conditions)

theorem mixedGenerators_perm {n : ℕ} (K : Type*) [CommRing K]
    (r : RankArray n) {a b : List (ℕ × ℕ)} (h : a.Perm b) :
    mixedGenerators K r a = mixedGenerators K r b := by
  ext f
  simp only [mixedGenerators, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (hf | ⟨ts, hts, hf⟩)
    · exact Or.inl hf
    · exact Or.inr ⟨ts, h.mem_iff.mp hts, hf⟩
  · rintro (hf | ⟨ts, hts, hf⟩)
    · exact Or.inl hf
    · exact Or.inr ⟨ts, h.mem_iff.mpr hts, hf⟩

theorem mixedIdeal_perm {n : ℕ} (K : Type*) [CommRing K]
    (r : RankArray n) {a b : List (ℕ × ℕ)} (h : a.Perm b) :
    mixedIdeal K r a = mixedIdeal K r b := by
  unfold mixedIdeal
  congr 1
  exact (h.map _).sum_eq

theorem filter_split_perm {α : Type*} (p : α → Bool) (l : List α) :
    ((l.filter p) ++ (l.filter fun x => !p x)).Perm l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases ha : p a = true
    · simpa [List.filter_cons, ha] using ih.cons a
    · have ha' : p a = false := Bool.eq_false_iff.mpr ha
      simp only [List.filter_cons, ha', Bool.false_eq_true, reduceIte,
        Bool.not_false, ↓reduceIte]
      have hm :
          ((l.filter p) ++ a :: l.filter (fun x => !p x)).Perm
            (a :: ((l.filter p) ++ l.filter (fun x => !p x))) := by
        simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using
          (show ((l.filter p) ++ [a]).Perm ([a] ++ l.filter p) from
            List.perm_append_comm).append_right
            (l.filter fun x => !p x)
      exact hm.trans (ih.cons a)

theorem mixedGroebner_prepend_ones {n : ℕ} (K : Type*) [Field K]
    (r : RankArray n) (ones rest : List (ℕ × ℕ))
    (hones : ∀ ts ∈ ones, ts.1 = 1)
    (hrest : (foldedOrder n).IsGroebnerBasis (mixedGenerators K r rest)
      (mixedIdeal K r rest)) :
    (foldedOrder n).IsGroebnerBasis (mixedGenerators K r (ones ++ rest))
      (mixedIdeal K r (ones ++ rest)) := by
  induction ones with
  | nil => simpa using hrest
  | cons a ones ih =>
    have ha : a.1 = 1 := hones a (by simp)
    have ht : ∀ ts ∈ ones, ts.1 = 1 := fun ts hts => hones ts (by simp [hts])
    obtain ⟨t, s⟩ := a
    dsimp only at ha
    subst t
    simpa using mixedGroebner_cons_one K r (ones ++ rest) s (ih ht)

theorem positiveCore_implies_compatible
    (hcore : PositiveCoreAssertion.{v}) : CompatibleGroebnerAssertion.{v} := by
  intro n K _ r hr conditions hvalid
  apply mixedGroebner_of_positiveBounds K r hr conditions
  let ones := conditions.filter fun ts => decide (ts.1 = 1)
  let rest := conditions.filter fun ts => !decide (ts.1 = 1)
  have hrestvalid : ValidSymbolicConditions n rest := by
    intro ts hts
    exact hvalid ts (List.mem_of_mem_filter hts)
  have hrestsize : ∀ ts ∈ rest, 2 ≤ ts.1 := by
    intro ts hts
    have h := List.mem_filter.mp hts
    have h1 := (hvalid ts h.1).1
    have hne : ts.1 ≠ 1 := by simpa using h.2
    omega
  have hposSym : ∀ i j, positiveBounds r i j = positiveBounds r j i := by
    intro i j
    simp only [positiveBounds, hr i j]
  have hpos : ∀ i j, 1 ≤ positiveBounds r i j := fun i j => le_max_right _ _
  have hrest := hcore n K (positiveBounds r) hposSym hpos rest hrestvalid hrestsize
  have hones : ∀ ts ∈ ones, ts.1 = 1 := by
    intro ts hts
    exact of_decide_eq_true (List.mem_filter.mp hts).2
  have h := mixedGroebner_prepend_ones K (positiveBounds r) ones rest hones hrest
  have hp : (ones ++ rest).Perm conditions := filter_split_perm _ conditions
  rw [mixedGenerators_perm K (positiveBounds r) hp,
    mixedIdeal_perm K (positiveBounds r) hp] at h
  exact h

/-- The literal integral/base-change conclusion follows from the same rational core. -/
theorem positiveCore_implies_integral
    (hcore : PositiveCoreAssertion.{0}) : IntegralBaseChangeAssertion.{v} :=
  integralBaseChangeAssertion_of_compatible (positiveCore_implies_compatible hcore)

end FourPapers.Symmetric.Reduction

end

noncomputable section


/- SOURCE Multisegment/YoungDiagram.lean -/
section
/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI-generated by Elazar Gershuni
-/

/-!
# Young-diagram row and cardinality utilities

Small extensions of Mathlib's `YoungDiagram` API used by the growth-diagram
formalization. They express containment, extensionality, first-row deletion,
and cardinality in terms of the canonical list of row lengths.
-/

namespace YoungDiagram

/-- Containment of Young diagrams is pointwise comparison of row lengths. -/
theorem le_iff_rowLen_le {μ ν : YoungDiagram} :
    μ ≤ ν ↔ ∀ i, μ.rowLen i ≤ ν.rowLen i := by
  constructor
  · intro h i
    by_contra hle
    have hlt : ν.rowLen i < μ.rowLen i := Nat.lt_of_not_ge hle
    have hmem : (i, ν.rowLen i) ∈ μ := mem_iff_lt_rowLen.mpr hlt
    exact (Nat.lt_irrefl _)
      (mem_iff_lt_rowLen.mp (h hmem))
  · intro h c hc
    rcases c with ⟨i, j⟩
    rw [mem_iff_lt_rowLen] at hc ⊢
    exact hc.trans_le (h i)

/-- Two Young diagrams are equal when all their row lengths agree. -/
@[ext]
theorem ext_rowLen {μ ν : YoungDiagram}
    (h : ∀ i, μ.rowLen i = ν.rowLen i) : μ = ν := by
  apply le_antisymm
  · exact le_iff_rowLen_le.mpr fun i ↦ (h i).le
  · exact le_iff_rowLen_le.mpr fun i ↦ (h i).ge

/-- Every row of the empty Young diagram has length zero. -/
@[simp]
theorem rowLen_bot (i : ℕ) : (⊥ : YoungDiagram).rowLen i = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hpos
  exact notMem_bot (i, 0) (mem_iff_lt_rowLen.mpr hpos)

/-- Reading past the canonical row-length list agrees with extending the row
length function by zero. -/
@[simp]
theorem getD_rowLens (μ : YoungDiagram) (i : ℕ) :
    μ.rowLens[i]?.getD 0 = μ.rowLen i := by
  rw [← List.getD_eq_getElem?_getD]
  by_cases hi : i < μ.rowLens.length
  · rw [List.getD_eq_getElem _ _ hi, get_rowLens]
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
    symm
    apply Nat.eq_zero_of_not_pos
    intro hpos
    apply hi
    rw [length_rowLens, ← mem_iff_lt_colLen, mem_iff_lt_rowLen]
    exact hpos

/-- The row-length function of `ofRowLens` is its input list extended by
zero. -/
@[simp]
theorem rowLen_ofRowLens_getD {w : List ℕ} {hw : w.SortedGE} (i : ℕ) :
    (ofRowLens w hw).rowLen i = w.getD i 0 := by
  by_cases hi : i < w.length
  · rw [rowLen_ofRowLens (i := ⟨i, hi⟩)]
    symm
    exact List.getD_eq_getElem _ _ hi
  · have hle : w.length ≤ i := Nat.le_of_not_gt hi
    rw [List.getD_eq_default _ _ hle]
    apply Nat.eq_zero_of_not_pos
    intro hpos
    have hmem : (i, 0) ∈ ofRowLens w hw :=
      mem_iff_lt_rowLen.mpr hpos
    exact hi (mem_ofRowLens.mp hmem).choose

/-- The Young diagram consisting of one column of the given height. -/
noncomputable def verticalColumn (height : ℕ) : YoungDiagram :=
  ofRowLens (List.replicate height 1) (by
    rw [List.sortedGE_iff_pairwise]
    simp)

/-- The canonical row lengths of a one-column diagram. -/
@[simp]
theorem rowLens_verticalColumn (height : ℕ) :
    (verticalColumn height).rowLens = List.replicate height 1 := by
  apply rowLens_ofRowLens_eq_self
  simp

/-- A row of a vertical column has length one below its height and zero
thereafter. -/
@[simp]
theorem rowLen_verticalColumn (height i : ℕ) :
    (verticalColumn height).rowLen i = if i < height then 1 else 0 := by
  rw [verticalColumn, rowLen_ofRowLens_getD]
  by_cases hi : i < height
  · rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
    simp [hi]

/-- Only the zeroth column of a vertical column is nonempty. -/
@[simp]
theorem colLen_verticalColumn (height j : ℕ) :
    (verticalColumn height).colLen j = if j = 0 then height else 0 := by
  cases j with
  | zero =>
      rw [← length_rowLens, rowLens_verticalColumn]
      simp
  | succ j =>
      simp only [Nat.succ_ne_zero, if_false]
      apply Nat.eq_zero_of_not_pos
      intro hpos
      have hmem : (0, j + 1) ∈ verticalColumn height :=
        mem_iff_lt_colLen.mpr hpos
      have hrow := mem_iff_lt_rowLen.mp hmem
      rw [rowLen_verticalColumn] at hrow
      split at hrow <;> omega

/-- The column of height zero is empty. -/
@[simp]
theorem verticalColumn_zero : verticalColumn 0 = ⊥ := by
  apply ext_rowLen
  intro i
  simp [verticalColumn]

/-- The Young diagram obtained by deleting the first row. -/
noncomputable def rowTail (μ : YoungDiagram) : YoungDiagram :=
  ofRowLens μ.rowLens.tail (by
    rw [List.sortedGE_iff_pairwise]
    exact (List.sortedGE_iff_pairwise.mp μ.rowLens_sorted).tail)

/-- The canonical row lengths after deleting the first row. -/
@[simp]
theorem rowLens_rowTail (μ : YoungDiagram) :
    μ.rowTail.rowLens = μ.rowLens.tail := by
  apply rowLens_ofRowLens_eq_self
  intro x hx
  exact μ.pos_of_mem_rowLens x (List.mem_of_mem_tail hx)

/-- Row `i` after deleting the first row was row `i + 1` originally. -/
@[simp]
theorem rowLen_rowTail (μ : YoungDiagram) (i : ℕ) :
    μ.rowTail.rowLen i = μ.rowLen (i + 1) := by
  rw [← getD_rowLens, rowLens_rowTail, ← getD_rowLens]
  cases μ.rowLens <;> simp

/-- A cell in the row tail is the corresponding cell one row lower in the
original diagram. -/
@[simp]
theorem mem_rowTail_iff (μ : YoungDiagram) (i j : ℕ) :
    (i, j) ∈ μ.rowTail ↔ (i + 1, j) ∈ μ := by
  simp only [mem_iff_lt_rowLen, rowLen_rowTail]

/-- The first canonical row length, totalized by zero, is `rowLen 0`. -/
theorem headD_rowLens (μ : YoungDiagram) :
    μ.rowLens.headD 0 = μ.rowLen 0 := by
  rw [← getD_rowLens]
  cases μ.rowLens <;> rfl

/-- A nonempty canonical row list decomposes into its first row and the row
list of `rowTail`. -/
theorem rowLens_eq_cons_rowLen_zero (μ : YoungDiagram)
    (hrows : μ.rowLens ≠ []) :
    μ.rowLens = μ.rowLen 0 :: μ.rowTail.rowLens := by
  rw [rowLens_rowTail]
  cases h : μ.rowLens with
  | nil => exact (hrows h).elim
  | cons a rows =>
      have hhead : a = μ.rowLen 0 := by
        simpa [h] using μ.headD_rowLens
      simp [hhead]

/-- Deleting the first row of the empty diagram remains empty. -/
@[simp]
theorem rowTail_bot : rowTail (⊥ : YoungDiagram) = ⊥ := by
  apply ext_rowLen
  simp

/-- A Young diagram is determined by its first row and its remaining rows. -/
theorem ext_rowLen_zero_rowTail {μ ν : YoungDiagram}
    (hzero : μ.rowLen 0 = ν.rowLen 0)
    (htail : μ.rowTail = ν.rowTail) : μ = ν := by
  apply ext_rowLen
  intro i
  cases i with
  | zero => exact hzero
  | succ i =>
      have h := congrArg (fun diagram : YoungDiagram => diagram.rowLen i) htail
      simpa [Nat.succ_eq_add_one] using h

/-- Equality of canonical row-length lists determines a Young diagram. -/
theorem ext_rowLens {μ ν : YoungDiagram}
    (hrows : μ.rowLens = ν.rowLens) : μ = ν := by
  apply ext_rowLen
  intro i
  rw [← getD_rowLens, ← getD_rowLens, hrows]

private theorem card_cellsOfRowLens (w : List ℕ) :
    (YoungDiagram.cellsOfRowLens w).card = w.sum := by
  induction w with
  | nil => simp [YoungDiagram.cellsOfRowLens]
  | cons a w ih =>
      rw [YoungDiagram.cellsOfRowLens, Finset.card_union_of_disjoint]
      · simp [ih]
      · rw [Finset.disjoint_left]
        rintro ⟨i, j⟩ hp hq
        simp only [Finset.mem_product, Finset.mem_singleton,
          Finset.mem_range] at hp
        obtain ⟨rfl, _⟩ := hp
        simp only [Finset.mem_map] at hq
        obtain ⟨q, _, hq⟩ := hq
        exact Nat.noConfusion (congrArg Prod.fst hq)

/-- The cardinality of a Young diagram constructed from row lengths is the
sum of those lengths. -/
@[simp]
theorem card_ofRowLens {w : List ℕ} {hw : w.SortedGE} :
    (ofRowLens w hw).card = w.sum :=
  card_cellsOfRowLens w

/-- The cardinality of a Young diagram is the sum of its canonical row
lengths. -/
theorem card_eq_sum_rowLens (μ : YoungDiagram) :
    μ.card = μ.rowLens.sum := by
  calc
    μ.card = (ofRowLens μ.rowLens μ.rowLens_sorted).card := by
      rw [ofRowLens_to_rowLens_eq_self]
    _ = μ.rowLens.sum := card_ofRowLens

/-- If every row has length at most `width`, the first `width` column
lengths account for every cell of the diagram. -/
theorem card_eq_sum_colLen_range_of_rowLen_le (μ : YoungDiagram)
    (width : ℕ) (hwidth : ∀ i, μ.rowLen i ≤ width) :
    μ.card = Finset.sum (Finset.range width) μ.colLen := by
  change μ.cells.card = _
  calc
    μ.cells.card = Finset.sum (Finset.range width)
        (fun j => (μ.cells.filter fun cell => cell.2 = j).card) := by
      apply Finset.card_eq_sum_card_fiberwise
      intro cell hcell
      change cell.2 ∈ Finset.range width
      rw [Finset.mem_range]
      have hmem : cell ∈ μ := (mem_cells cell).mp hcell
      exact (mem_iff_lt_rowLen.mp hmem).trans_le (hwidth cell.1)
    _ = Finset.sum (Finset.range width) μ.colLen := by
      apply Finset.sum_congr rfl
      intro j _
      rw [μ.colLen_eq_card]
      apply congrArg Finset.card
      ext cell
      simp only [Finset.mem_filter, mem_cells, mem_col_iff]

/-- A one-column diagram has one cell at each level below its height. -/
@[simp]
theorem card_verticalColumn (height : ℕ) :
    (verticalColumn height).card = height := by
  rw [card_eq_sum_rowLens, rowLens_verticalColumn]
  simp


end YoungDiagram

end


/- SOURCE Multisegment/Greene/Word.lean -/
section
/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI-generated by Elazar Gershuni
-/

/-!
# Finite-word Greene supports

This file is the word-level classical layer in the standardization proof of
the Burge--Greene theorem.  A support is a family of weakly decreasing
subsequences of a finite word.  As in `IsOccurrenceKSupport`, the blocks need
not be declared disjoint: their union is scored, and overlaps never improve
the score.

The fixed-length function representation avoids casts when applying local
dual Knuth moves.  Matrix occurrence words will later be obtained by choosing
an enumeration of `MatrixOccurrence A`.
-/

namespace Multisegment

/-- A word of fixed finite length. -/
abbrev FiniteWord (α : Type*) (n : ℕ) := Fin n → α

/-- A set of positions is a weakly decreasing subsequence of a word. -/
noncomputable def IsWeaklyDecreasingSubsequence {α : Type*} [LE α] {n : ℕ}
    (w : FiniteWord α n) (S : Finset (Fin n)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i < j → w j ≤ w i

instance {α : Type*} [LE α]
    [DecidableRel (fun x y : α => x ≤ y)] {n : ℕ}
    (w : FiniteWord α n) :
    DecidablePred (IsWeaklyDecreasingSubsequence w) := fun S =>
  inferInstanceAs
    (Decidable (∀ i ∈ S, ∀ j ∈ S, i < j → w j ≤ w i))

/-- A `J`-support of a word is a `J`-indexed family of weakly decreasing
subsequences. -/
noncomputable def IsWordKSupport {α : Type*} [LE α] {n J : ℕ}
    (w : FiniteWord α n) (P : Fin J → Finset (Fin n)) : Prop :=
  ∀ k, IsWeaklyDecreasingSubsequence w (P k)

instance {α : Type*} [LE α]
    [DecidableRel (fun x y : α => x ≤ y)] {n J : ℕ}
    (w : FiniteWord α n) : DecidablePred (IsWordKSupport (J := J) w) :=
  fun P => inferInstanceAs
    (Decidable (∀ k, IsWeaklyDecreasingSubsequence w (P k)))

/-- The positions covered by a word `J`-support. -/
noncomputable def wordKSupportCover {n J : ℕ} (P : Fin J → Finset (Fin n)) :
    Finset (Fin n) :=
  Finset.univ.biUnion P

/-- The maximum number of positions covered by `J` weakly decreasing
subsequences. -/
noncomputable def wordGreeneMax {α : Type*} [LE α]
    [DecidableRel (fun x y : α => x ≤ y)] {n : ℕ}
    (w : FiniteWord α n) (J : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin J → Finset (Fin n))).filter
      (IsWordKSupport w)).sup fun P => (wordKSupportCover P).card

/-- A disjoint `J`-support encoded by assigning each covered position one
color. -/
abbrev WordColoring (n J : ℕ) := Fin n → Option (Fin J)

/-- The positions carrying one color. -/
noncomputable def wordColorBlock {n J : ℕ} (φ : WordColoring n J) (k : Fin J) :
    Finset (Fin n) :=
  Finset.univ.filter fun i => φ i = some k

@[simp]
theorem mem_wordColorBlock {n J : ℕ} {φ : WordColoring n J}
    {k : Fin J} {i : Fin n} :
    i ∈ wordColorBlock φ k ↔ φ i = some k := by
  simp [wordColorBlock]

/-- A coloring is admissible when every color class is a weakly decreasing
subsequence. -/
noncomputable def IsWordColoringSupport {α : Type*} [LE α] {n J : ℕ}
    (w : FiniteWord α n) (φ : WordColoring n J) : Prop :=
  ∀ k, IsWeaklyDecreasingSubsequence w (wordColorBlock φ k)

instance {α : Type*} [LE α]
    [DecidableRel (fun x y : α => x ≤ y)] {n J : ℕ}
    (w : FiniteWord α n) : DecidablePred (IsWordColoringSupport (J := J) w) :=
  fun φ => inferInstanceAs
    (Decidable (∀ k, IsWeaklyDecreasingSubsequence w (wordColorBlock φ k)))

/-- The set of colored word positions. -/
noncomputable def wordColoringCover {n J : ℕ} (φ : WordColoring n J) : Finset (Fin n) :=
  Finset.univ.filter fun i => (φ i).isSome

@[simp]
theorem mem_wordColoringCover {n J : ℕ} {φ : WordColoring n J}
    {i : Fin n} :
    i ∈ wordColoringCover φ ↔ (φ i).isSome := by
  simp [wordColoringCover]

/-- Greene maximum in the disjoint coloring presentation. -/
noncomputable def wordColoringGreeneMax {α : Type*} [LE α]
    [DecidableRel (fun x y : α => x ≤ y)] {n : ℕ}
    (w : FiniteWord α n) (J : ℕ) : ℕ :=
  ((Finset.univ : Finset (WordColoring n J)).filter
      (IsWordColoringSupport w)).sup fun φ => (wordColoringCover φ).card

/-- Forgetting the disjoint encoding gives an ordinary word support. -/
theorem isWordKSupport_wordColorBlock {α : Type*} [LE α] {n J : ℕ}
    {w : FiniteWord α n} {φ : WordColoring n J}
    (hφ : IsWordColoringSupport w φ) :
    IsWordKSupport w (wordColorBlock φ) :=
  hφ

/-- The family of color classes covers exactly the colored positions. -/
@[simp]
theorem wordKSupportCover_wordColorBlock {n J : ℕ}
    (φ : WordColoring n J) :
    wordKSupportCover (wordColorBlock φ) = wordColoringCover φ := by
  ext i
  simp [wordKSupportCover, Option.isSome_iff_exists]

/-- Disjoint colorings are no stronger than arbitrary support families. -/
theorem wordColoringGreeneMax_le_wordGreeneMax
    {α : Type*} [LE α] [DecidableRel (fun x y : α => x ≤ y)]
    {n : ℕ} (w : FiniteWord α n) (J : ℕ) :
    wordColoringGreeneMax w J ≤ wordGreeneMax w J := by
  unfold wordColoringGreeneMax
  apply Finset.sup_le
  intro φ hφ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hφ
  rw [← wordKSupportCover_wordColorBlock]
  unfold wordGreeneMax
  exact Finset.le_sup
    (f := fun P : Fin J → Finset (Fin n) => (wordKSupportCover P).card)
    (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, isWordKSupport_wordColorBlock hφ⟩)

/-- Assign a covered position to the least support block containing it. -/
noncomputable def coloringOfWordKSupport {n J : ℕ}
    (P : Fin J → Finset (Fin n)) : WordColoring n J := fun i =>
  let colors := Finset.univ.filter fun k => i ∈ P k
  if h : colors.Nonempty then some (colors.min' h) else none

/-- A chosen color really is one of the original blocks containing the
position. -/
theorem mem_of_coloringOfWordKSupport_eq_some {n J : ℕ}
    {P : Fin J → Finset (Fin n)} {i : Fin n} {k : Fin J}
    (hik : coloringOfWordKSupport P i = some k) :
    i ∈ P k := by
  unfold coloringOfWordKSupport at hik
  dsimp only at hik
  split at hik
  · rename_i hne
    have hmem := Finset.min'_mem
      (Finset.univ.filter fun l => i ∈ P l) hne
    have heq := Option.some.inj hik
    rw [heq] at hmem
    exact (Finset.mem_filter.mp hmem).2
  · simp at hik

/-- Choosing the least containing block preserves the covered set exactly. -/
@[simp]
theorem wordColoringCover_coloringOfWordKSupport {n J : ℕ}
    (P : Fin J → Finset (Fin n)) :
    wordColoringCover (coloringOfWordKSupport P) = wordKSupportCover P := by
  ext i
  rw [mem_wordColoringCover]
  constructor
  · intro hi
    rw [Option.isSome_iff_exists] at hi
    obtain ⟨k, hik⟩ := hi
    apply Finset.mem_biUnion.mpr
    exact ⟨k, Finset.mem_univ k,
      mem_of_coloringOfWordKSupport_eq_some hik⟩
  · intro hi
    obtain ⟨k, _hk, hik⟩ := Finset.mem_biUnion.mp hi
    unfold coloringOfWordKSupport
    dsimp only
    have hne : (Finset.univ.filter fun l => i ∈ P l).Nonempty :=
      ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hik⟩⟩
    simp [hne]

/-- Least-block normalization preserves subsequence admissibility. -/
theorem isWordColoringSupport_coloringOfWordKSupport
    {α : Type*} [LE α] {n J : ℕ} {w : FiniteWord α n}
    {P : Fin J → Finset (Fin n)} (hP : IsWordKSupport w P) :
    IsWordColoringSupport w (coloringOfWordKSupport P) := by
  intro k i hi j hj hij
  rw [mem_wordColorBlock] at hi hj
  exact hP k i (mem_of_coloringOfWordKSupport_eq_some hi)
    j (mem_of_coloringOfWordKSupport_eq_some hj) hij

/-- Every support family has a disjoint coloring with the same cover. -/
theorem wordGreeneMax_le_wordColoringGreeneMax
    {α : Type*} [LE α] [DecidableRel (fun x y : α => x ≤ y)]
    {n : ℕ} (w : FiniteWord α n) (J : ℕ) :
    wordGreeneMax w J ≤ wordColoringGreeneMax w J := by
  unfold wordGreeneMax
  apply Finset.sup_le
  intro P hP
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP
  rw [← wordColoringCover_coloringOfWordKSupport]
  unfold wordColoringGreeneMax
  exact Finset.le_sup
    (f := fun φ : WordColoring n J => (wordColoringCover φ).card)
    (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,
        isWordColoringSupport_coloringOfWordKSupport hP⟩)

/-- The family and disjoint-coloring presentations of word Greene supports
have the same optimum. -/
theorem wordColoringGreeneMax_eq_wordGreeneMax
    {α : Type*} [LE α] [DecidableRel (fun x y : α => x ≤ y)]
    {n : ℕ} (w : FiniteWord α n) (J : ℕ) :
    wordColoringGreeneMax w J = wordGreeneMax w J :=
  Nat.le_antisymm
    (wordColoringGreeneMax_le_wordGreeneMax w J)
    (wordGreeneMax_le_wordColoringGreeneMax w J)

/-! ## Reindexing word positions -/

/-- Pull a word back along a permutation of its positions. -/
noncomputable def permuteFiniteWord {α : Type*} {n : ℕ} (e : Equiv.Perm (Fin n))
    (w : FiniteWord α n) : FiniteWord α n :=
  w ∘ e

/-- Pull a coloring back along a permutation of word positions. -/
noncomputable def permuteWordColoring {n J : ℕ} (e : Equiv.Perm (Fin n))
    (φ : WordColoring n J) : WordColoring n J :=
  φ ∘ e

/-- Reindexing positions preserves the number of covered positions. -/
theorem card_wordColoringCover_permute {n J : ℕ}
    (e : Equiv.Perm (Fin n)) (φ : WordColoring n J) :
    (wordColoringCover (permuteWordColoring e φ)).card =
      (wordColoringCover φ).card := by
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi
    rw [mem_wordColoringCover] at hi ⊢
    exact hi
  · intro i _ j _ hij
    exact e.injective hij
  · intro j hj
    refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
    rw [mem_wordColoringCover] at hj ⊢
    simpa [permuteWordColoring] using hj

/-- Swap the adjacent positions `p` and `p + 1` of a finite word. -/
noncomputable def adjacentPositionSwap {n : ℕ} (p : ℕ) (hp : p + 1 < n) :
    Equiv.Perm (Fin n) :=
  Equiv.swap ⟨p, by omega⟩ ⟨p + 1, hp⟩

@[simp]
theorem adjacentPositionSwap_left {n p : ℕ} (hp : p + 1 < n) :
    adjacentPositionSwap p hp ⟨p, by omega⟩ = ⟨p + 1, hp⟩ := by
  simp [adjacentPositionSwap]

@[simp]
theorem adjacentPositionSwap_right {n p : ℕ} (hp : p + 1 < n) :
    adjacentPositionSwap p hp ⟨p + 1, hp⟩ = ⟨p, by omega⟩ := by
  simp [adjacentPositionSwap]

@[simp]
theorem adjacentPositionSwap_apply_of_ne {n p : ℕ} (hp : p + 1 < n)
    (i : Fin n) (hi₀ : i.val ≠ p) (hi₁ : i.val ≠ p + 1) :
    adjacentPositionSwap p hp i = i := by
  apply Equiv.swap_apply_of_ne_of_ne
  · exact fun h => hi₀ (congrArg Fin.val h)
  · exact fun h => hi₁ (congrArg Fin.val h)

/-- Numeric description of an adjacent position swap. -/
theorem adjacentPositionSwap_val {n p : ℕ} (hp : p + 1 < n)
    (i : Fin n) :
    (adjacentPositionSwap p hp i).val =
      if i.val = p then p + 1 else if i.val = p + 1 then p else i.val := by
  by_cases hi₀ : i.val = p
  · have hi : i = ⟨p, by omega⟩ := Fin.ext hi₀
    rw [hi]
    simp
  · by_cases hi₁ : i.val = p + 1
    · have hi : i = ⟨p + 1, hp⟩ := Fin.ext hi₁
      rw [hi]
      simp
    · rw [adjacentPositionSwap_apply_of_ne hp i hi₀ hi₁]
      simp [hi₀, hi₁]

/-- An adjacent swap preserves the order of every pair except the swapped
pair itself. -/
theorem adjacentPositionSwap_lt_of_not_pair {n p : ℕ} (hp : p + 1 < n)
    {i j : Fin n} (hij : i < j)
    (hpair : ¬ (i.val = p ∧ j.val = p + 1)) :
    adjacentPositionSwap p hp i < adjacentPositionSwap p hp j := by
  rw [Fin.lt_def, adjacentPositionSwap_val hp,
    adjacentPositionSwap_val hp]
  rw [Fin.lt_def] at hij
  split_ifs <;> omega

/-- Pulling back a support along an adjacent swap is admissible provided the
two swapped source positions do not have the same color. -/
theorem isWordColoringSupport_permute_adjacent_of_ne
    {α : Type*} [LE α] {n J p : ℕ} (hp : p + 1 < n)
    {w : FiniteWord α n} {φ : WordColoring n J}
    (hφ : IsWordColoringSupport w φ)
    (hne : ∀ k : Fin J,
      ¬ (φ ⟨p, by omega⟩ = some k ∧ φ ⟨p + 1, hp⟩ = some k)) :
    IsWordColoringSupport
      (permuteFiniteWord (adjacentPositionSwap p hp) w)
      (permuteWordColoring (adjacentPositionSwap p hp) φ) := by
  intro k i hi j hj hij
  have hi' : φ (adjacentPositionSwap p hp i) = some k := by
    simpa [permuteWordColoring] using (mem_wordColorBlock.mp hi)
  have hj' : φ (adjacentPositionSwap p hp j) = some k := by
    simpa [permuteWordColoring] using (mem_wordColorBlock.mp hj)
  by_cases hpair : i.val = p ∧ j.val = p + 1
  · have hiEq : i = ⟨p, by omega⟩ := Fin.ext hpair.1
    have hjEq : j = ⟨p + 1, hp⟩ := Fin.ext hpair.2
    rw [hiEq, adjacentPositionSwap_left] at hi'
    rw [hjEq, adjacentPositionSwap_right] at hj'
    exact False.elim ((hne k) ⟨hj', hi'⟩)
  · have hlt := adjacentPositionSwap_lt_of_not_pair hp hij hpair
    change w (adjacentPositionSwap p hp j) ≤
      w (adjacentPositionSwap p hp i)
    exact hφ k _ (mem_wordColorBlock.mpr hi') _
      (mem_wordColorBlock.mpr hj') hlt

/-! ## Dual Knuth moves -/

/-- Easy direction of the dual Knuth move
`b a c -> b c a` under `a ≤ b < c`: the increasing adjacent pair cannot
already have one color. -/
theorem isWordColoringSupport_dualKnuthTwo_forward
    {α : Type*} [LinearOrder α] {n J p : ℕ} (hp : p + 2 < n)
    {w : FiniteWord α n} {φ : WordColoring n J}
    (hab : w ⟨p + 1, by omega⟩ ≤ w ⟨p, by omega⟩)
    (hbc : w ⟨p, by omega⟩ < w ⟨p + 2, hp⟩)
    (hφ : IsWordColoringSupport w φ) :
    IsWordColoringSupport
      (permuteFiniteWord (adjacentPositionSwap (p + 1) (by omega)) w)
      (permuteWordColoring (adjacentPositionSwap (p + 1) (by omega)) φ) := by
  apply isWordColoringSupport_permute_adjacent_of_ne (p := p + 1)
    (by omega) hφ
  intro k hk
  have hdec := hφ k ⟨p + 1, by omega⟩
    (mem_wordColorBlock.mpr hk.1) ⟨p + 2, hp⟩
    (mem_wordColorBlock.mpr hk.2) (by simp)
  exact (not_le_of_gt (hab.trans_lt hbc)) hdec

/-- In the hard reverse move with an uncolored pivot, move the final local
position onto that pivot. -/
noncomputable def dualKnuthTwoVacantColoring {n J p : ℕ} (hp : p + 2 < n)
    (φ : WordColoring n J) : WordColoring n J :=
  permuteWordColoring
    (Equiv.swap (⟨p, by omega⟩ : Fin n) ⟨p + 2, hp⟩) φ

@[simp]
theorem dualKnuthTwoVacantColoring_pivot {n J p : ℕ} (hp : p + 2 < n)
    (φ : WordColoring n J) :
    dualKnuthTwoVacantColoring hp φ ⟨p, by omega⟩ = φ ⟨p + 2, hp⟩ := by
  simp [dualKnuthTwoVacantColoring, permuteWordColoring]

@[simp]
theorem dualKnuthTwoVacantColoring_final {n J p : ℕ} (hp : p + 2 < n)
    (φ : WordColoring n J) :
    dualKnuthTwoVacantColoring hp φ ⟨p + 2, hp⟩ = φ ⟨p, by omega⟩ := by
  simp [dualKnuthTwoVacantColoring, permuteWordColoring]

@[simp]
theorem dualKnuthTwoVacantColoring_of_ne {n J p : ℕ} (hp : p + 2 < n)
    (φ : WordColoring n J) (i : Fin n)
    (hi₀ : i.val ≠ p) (hi₂ : i.val ≠ p + 2) :
    dualKnuthTwoVacantColoring hp φ i = φ i := by
  unfold dualKnuthTwoVacantColoring permuteWordColoring
  apply congrArg φ
  apply Equiv.swap_apply_of_ne_of_ne
  · exact fun h => hi₀ (congrArg Fin.val h)
  · exact fun h => hi₂ (congrArg Fin.val h)

theorem card_wordColoringCover_dualKnuthTwoVacantColoring
    {n J p : ℕ} (hp : p + 2 < n) (φ : WordColoring n J) :
    (wordColoringCover (dualKnuthTwoVacantColoring hp φ)).card =
      (wordColoringCover φ).card :=
  card_wordColoringCover_permute _ φ

/-- Hard reverse direction of `b a c -> b c a` when the pivot `b` is not
covered.  The target block containing `c,a` is changed to contain `b,a`;
all other blocks are unchanged. -/
theorem isWordColoringSupport_dualKnuthTwo_vacant
    {α : Type*} [LinearOrder α] {n J p : ℕ} (hp : p + 2 < n)
    {w : FiniteWord α n} {φ : WordColoring n J} {s : Fin J}
    (hab : w ⟨p + 1, by omega⟩ ≤ w ⟨p, by omega⟩)
    (hbc : w ⟨p, by omega⟩ < w ⟨p + 2, hp⟩)
    (hφ : IsWordColoringSupport
      (permuteFiniteWord (adjacentPositionSwap (p + 1) (by omega)) w) φ)
    (hs₁ : φ ⟨p + 1, by omega⟩ = some s)
    (hs₂ : φ ⟨p + 2, hp⟩ = some s)
    (hzero : φ ⟨p, by omega⟩ = none) :
    IsWordColoringSupport w (dualKnuthTwoVacantColoring hp φ) := by
  intro k i hi j hj hij
  rw [mem_wordColorBlock] at hi hj
  have hi₂ : i.val ≠ p + 2 := by
    intro hiEq
    have hiFin : i = ⟨p + 2, hp⟩ := Fin.ext hiEq
    rw [hiFin, dualKnuthTwoVacantColoring_final, hzero] at hi
    simp at hi
  have hj₂ : j.val ≠ p + 2 := by
    intro hjEq
    have hjFin : j = ⟨p + 2, hp⟩ := Fin.ext hjEq
    rw [hjFin, dualKnuthTwoVacantColoring_final, hzero] at hj
    simp at hj
  by_cases hks : k = s
  · subst k
    have original_of_ne_p (x : Fin n) (hx : x.val ≠ p)
        (hx₂ : x.val ≠ p + 2)
        (hxs : dualKnuthTwoVacantColoring hp φ x = some s) :
        φ x = some s := by
      rw [dualKnuthTwoVacantColoring_of_ne hp φ x hx hx₂] at hxs
      exact hxs
    have prefix_bound (x : Fin n) (hx : x.val < p)
        (hxs : dualKnuthTwoVacantColoring hp φ x = some s) :
        w ⟨p + 2, hp⟩ ≤ w x := by
      have hxφ : φ x = some s :=
        original_of_ne_p x (by omega) (by omega) hxs
      have hdec := hφ s x (mem_wordColorBlock.mpr hxφ)
        ⟨p + 1, by omega⟩ (mem_wordColorBlock.mpr hs₁) (by
          change x.val < p + 1
          omega)
      change w (adjacentPositionSwap (p + 1) (by omega)
          ⟨p + 1, by omega⟩) ≤
        w (adjacentPositionSwap (p + 1) (by omega) x) at hdec
      rw [adjacentPositionSwap_left] at hdec
      rw [adjacentPositionSwap_apply_of_ne] at hdec
      · exact hdec
      · omega
      · omega
    have suffix_bound (x : Fin n) (hx : p + 2 < x.val)
        (hxs : dualKnuthTwoVacantColoring hp φ x = some s) :
        w x ≤ w ⟨p + 1, by omega⟩ := by
      have hxφ : φ x = some s :=
        original_of_ne_p x (by omega) (by omega) hxs
      have hdec := hφ s ⟨p + 2, hp⟩
        (mem_wordColorBlock.mpr hs₂) x (mem_wordColorBlock.mpr hxφ)
        (by
          change p + 2 < x.val
          exact hx)
      change w (adjacentPositionSwap (p + 1) (by omega) x) ≤
        w (adjacentPositionSwap (p + 1) (by omega)
          ⟨p + 2, hp⟩) at hdec
      rw [adjacentPositionSwap_right] at hdec
      rw [adjacentPositionSwap_apply_of_ne] at hdec
      · exact hdec
      · omega
      · omega
    have unchanged_pair (x y : Fin n) (hxy : x < y)
        (hx₀ : x.val ≠ p) (hy₀ : y.val ≠ p)
        (hx₁ : x.val ≠ p + 1) (hy₁ : y.val ≠ p + 1)
        (hx₂ : x.val ≠ p + 2) (hy₂ : y.val ≠ p + 2)
        (hxs : dualKnuthTwoVacantColoring hp φ x = some s)
        (hys : dualKnuthTwoVacantColoring hp φ y = some s) :
        w y ≤ w x := by
      have hxφ : φ x = some s := original_of_ne_p x hx₀ hx₂ hxs
      have hyφ : φ y = some s := original_of_ne_p y hy₀ hy₂ hys
      have hdec := hφ s x (mem_wordColorBlock.mpr hxφ)
        y (mem_wordColorBlock.mpr hyφ) hxy
      change w (adjacentPositionSwap (p + 1) (by omega) y) ≤
        w (adjacentPositionSwap (p + 1) (by omega) x) at hdec
      rw [adjacentPositionSwap_apply_of_ne (by omega) x hx₁ hx₂,
        adjacentPositionSwap_apply_of_ne (by omega) y hy₁ hy₂] at hdec
      exact hdec
    by_cases hip : i.val < p
    · by_cases hjp : j.val < p
      · exact unchanged_pair i j hij (by omega) (by omega) (by omega)
          (by omega) hi₂ hj₂ hi hj
      · have hprefix := prefix_bound i hip hi
        by_cases hj₀ : j.val = p
        · have hjFin : j = ⟨p, by omega⟩ := Fin.ext hj₀
          rw [hjFin]
          exact le_trans (le_of_lt hbc) hprefix
        · by_cases hj₁ : j.val = p + 1
          · have hjFin : j = ⟨p + 1, by omega⟩ := Fin.ext hj₁
            rw [hjFin]
            exact le_trans (hab.trans (le_of_lt hbc)) hprefix
          · have hjgt : p + 2 < j.val := by omega
            exact (suffix_bound j hjgt hj).trans
              (hab.trans (le_of_lt hbc) |>.trans hprefix)
    · by_cases hi₀ : i.val = p
      · have hiFin : i = ⟨p, by omega⟩ := Fin.ext hi₀
        by_cases hj₁ : j.val = p + 1
        · have hjFin : j = ⟨p + 1, by omega⟩ := Fin.ext hj₁
          simpa [hiFin, hjFin] using hab
        · have hjgt : p + 2 < j.val := by omega
          have hsuf := suffix_bound j hjgt hj
          rw [hiFin]
          exact hsuf.trans hab
      · by_cases hi₁ : i.val = p + 1
        · have hiFin : i = ⟨p + 1, by omega⟩ := Fin.ext hi₁
          have hjgt : p + 2 < j.val := by omega
          rw [hiFin]
          exact suffix_bound j hjgt hj
        · have higt : p + 2 < i.val := by omega
          have hjgt : p + 2 < j.val := by omega
          exact unchanged_pair i j hij (by omega) (by omega) (by omega)
            (by omega) hi₂ hj₂ hi hj
  · have off_triple (x : Fin n)
        (hx : dualKnuthTwoVacantColoring hp φ x = some k) :
        x.val ≠ p ∧ x.val ≠ p + 1 ∧ x.val ≠ p + 2 := by
      constructor
      · intro hx₀
        have hxFin : x = ⟨p, by omega⟩ := Fin.ext hx₀
        rw [hxFin, dualKnuthTwoVacantColoring_pivot, hs₂] at hx
        exact hks (Option.some.inj hx).symm
      · constructor
        · intro hx₁
          have hxFin : x = ⟨p + 1, by omega⟩ := Fin.ext hx₁
          have heval : dualKnuthTwoVacantColoring hp φ
              ⟨p + 1, by omega⟩ = φ ⟨p + 1, by omega⟩ :=
            dualKnuthTwoVacantColoring_of_ne hp φ _ (by omega) (by omega)
          rw [hxFin, heval, hs₁] at hx
          exact hks (Option.some.inj hx).symm
        · intro hx₂
          have hxFin : x = ⟨p + 2, hp⟩ := Fin.ext hx₂
          rw [hxFin, dualKnuthTwoVacantColoring_final, hzero] at hx
          simp at hx
    have hiOff := off_triple i hi
    have hjOff := off_triple j hj
    have hiφ : φ i = some k := by
      rwa [dualKnuthTwoVacantColoring_of_ne hp φ i hiOff.1 hiOff.2.2] at hi
    have hjφ : φ j = some k := by
      rwa [dualKnuthTwoVacantColoring_of_ne hp φ j hjOff.1 hjOff.2.2] at hj
    have hdec := hφ k i (mem_wordColorBlock.mpr hiφ)
      j (mem_wordColorBlock.mpr hjφ) hij
    change w (adjacentPositionSwap (p + 1) (by omega) j) ≤
      w (adjacentPositionSwap (p + 1) (by omega) i) at hdec
    rw [adjacentPositionSwap_apply_of_ne (by omega) i hiOff.2.1
        hiOff.2.2,
      adjacentPositionSwap_apply_of_ne (by omega) j hjOff.2.1
        hjOff.2.2] at hdec
    exact hdec

/-- Exchange two color names, leaving `none` and every other color fixed. -/
noncomputable def swapWordColors {J : ℕ} (s t : Fin J) : Option (Fin J) → Option (Fin J)
  | some k => if k = s then some t else if k = t then some s else some k
  | none => none

@[simp]
theorem swapWordColors_isSome {J : ℕ} (s t : Fin J) (o : Option (Fin J)) :
    (swapWordColors s t o).isSome = o.isSome := by
  cases o with
  | none => rfl
  | some k =>
      simp only [swapWordColors]
      by_cases hks : k = s
      · rw [if_pos hks]
        rfl
      · rw [if_neg hks]
        by_cases hkt : k = t
        · rw [if_pos hkt]
          rfl
        · rw [if_neg hkt]

/-- In the hard reverse move with a covered pivot, splice the suffixes of
the pivot color `t` and the local-pair color `s`.  The last local position
is the seam and remains colored `s`. -/
noncomputable def dualKnuthTwoOccupiedColoring {n J p : ℕ} (_hp : p + 2 < n)
    (s t : Fin J) (φ : WordColoring n J) : WordColoring n J := fun i =>
  if i.val ≤ p then φ i
  else if i.val = p + 2 then φ i
  else swapWordColors s t (φ i)

@[simp]
theorem dualKnuthTwoOccupiedColoring_of_le {n J p : ℕ} (hp : p + 2 < n)
    (s t : Fin J) (φ : WordColoring n J) (i : Fin n) (hi : i.val ≤ p) :
    dualKnuthTwoOccupiedColoring hp s t φ i = φ i := by
  simp [dualKnuthTwoOccupiedColoring, hi]

@[simp]
theorem dualKnuthTwoOccupiedColoring_seam {n J p : ℕ} (hp : p + 2 < n)
    (s t : Fin J) (φ : WordColoring n J) :
    dualKnuthTwoOccupiedColoring hp s t φ ⟨p + 2, hp⟩ =
      φ ⟨p + 2, hp⟩ := by
  simp [dualKnuthTwoOccupiedColoring]

@[simp]
theorem dualKnuthTwoOccupiedColoring_of_lt_of_ne
    {n J p : ℕ} (hp : p + 2 < n) (s t : Fin J)
    (φ : WordColoring n J) (i : Fin n) (hi : p < i.val)
    (hne : i.val ≠ p + 2) :
    dualKnuthTwoOccupiedColoring hp s t φ i =
      swapWordColors s t (φ i) := by
  simp [dualKnuthTwoOccupiedColoring, Nat.not_le.mpr hi, hne]

/-- Occupied-pivot suffix splicing changes only color names, never coverage. -/
@[simp]
theorem wordColoringCover_dualKnuthTwoOccupiedColoring
    {n J p : ℕ} (hp : p + 2 < n) (s t : Fin J)
    (φ : WordColoring n J) :
    wordColoringCover (dualKnuthTwoOccupiedColoring hp s t φ) =
      wordColoringCover φ := by
  ext i
  rw [mem_wordColoringCover, mem_wordColoringCover]
  by_cases hle : i.val ≤ p
  · simp [dualKnuthTwoOccupiedColoring, hle]
  · by_cases heq : i.val = p + 2
    · simp [dualKnuthTwoOccupiedColoring, heq]
    · simp [dualKnuthTwoOccupiedColoring, hle, heq]

@[simp]
theorem swapWordColors_eq_some_left_iff {J : ℕ} {s t : Fin J}
    (hst : s ≠ t) (o : Option (Fin J)) :
    swapWordColors s t o = some s ↔ o = some t := by
  cases o with
  | none => simp [swapWordColors]
  | some k =>
      by_cases hks : k = s
      · subst k
        simp [swapWordColors, hst, hst.symm]
      · by_cases hkt : k = t
        · subst k
          simp [swapWordColors, hst.symm]
        · simp [swapWordColors, hks, hkt]

@[simp]
theorem swapWordColors_eq_some_right_iff {J : ℕ} {s t : Fin J}
    (hst : s ≠ t) (o : Option (Fin J)) :
    swapWordColors s t o = some t ↔ o = some s := by
  cases o with
  | none => simp [swapWordColors]
  | some k =>
      by_cases hks : k = s
      · subst k
        simp [swapWordColors]
      · by_cases hkt : k = t
        · subst k
          simp [swapWordColors, hst, hst.symm]
        · simp [swapWordColors, hks, hkt]

@[simp]
theorem swapWordColors_eq_some_other_iff {J : ℕ} {s t k : Fin J}
    (hks : k ≠ s) (hkt : k ≠ t) (o : Option (Fin J)) :
    swapWordColors s t o = some k ↔ o = some k := by
  cases o with
  | none => simp [swapWordColors]
  | some l =>
      by_cases hls : l = s
      · subst l
        simp [swapWordColors, hks.symm, hkt.symm]
      · by_cases hlt : l = t
        · subst l
          simp [swapWordColors, hls, hks.symm, hkt.symm]
        · simp [swapWordColors, hls, hlt]

/-- Hard reverse direction of `b a c -> b c a` when the pivot has another
color.  The two relevant color classes are spliced across the local triple. -/
theorem isWordColoringSupport_dualKnuthTwo_occupied
    {α : Type*} [LinearOrder α] {n J p : ℕ} (hp : p + 2 < n)
    {w : FiniteWord α n} {φ : WordColoring n J} {s t : Fin J}
    (hab : w ⟨p + 1, by omega⟩ ≤ w ⟨p, by omega⟩)
    (hbc : w ⟨p, by omega⟩ < w ⟨p + 2, hp⟩)
    (hφ : IsWordColoringSupport
      (permuteFiniteWord (adjacentPositionSwap (p + 1) (by omega)) w) φ)
    (ht : φ ⟨p, by omega⟩ = some t)
    (hs₁ : φ ⟨p + 1, by omega⟩ = some s)
    (hs₂ : φ ⟨p + 2, hp⟩ = some s) :
    IsWordColoringSupport w
      (dualKnuthTwoOccupiedColoring hp s t φ) := by
  have hst : s ≠ t := by
    intro h
    subst t
    have hdec := hφ s ⟨p, by omega⟩ (mem_wordColorBlock.mpr ht)
      ⟨p + 1, by omega⟩ (mem_wordColorBlock.mpr hs₁) (by
        change p < p + 1
        omega)
    change w (adjacentPositionSwap (p + 1) (by omega)
        ⟨p + 1, by omega⟩) ≤
      w (adjacentPositionSwap (p + 1) (by omega) ⟨p, by omega⟩) at hdec
    rw [adjacentPositionSwap_left,
      adjacentPositionSwap_apply_of_ne (by omega) _ (by simp) (by
        change p ≠ p + 1 + 1
        omega)] at hdec
    exact (not_le_of_gt hbc) hdec
  intro k i hi j hj hij
  rw [mem_wordColorBlock] at hi hj
  by_cases hks : k = s
  · subst k
    have class_s (x : Fin n)
        (hx : dualKnuthTwoOccupiedColoring hp s t φ x = some s) :
        x.val < p ∨ x.val = p + 2 ∨ p + 2 < x.val := by
      have hxp : x.val ≠ p := by
        intro heq
        have hxFin : x = ⟨p, by omega⟩ := Fin.ext heq
        rw [hxFin, dualKnuthTwoOccupiedColoring_of_le hp s t φ _ (by simp),
          ht] at hx
        exact hst (Option.some.inj hx).symm
      have hxp1 : x.val ≠ p + 1 := by
        intro heq
        have hxFin : x = ⟨p + 1, by omega⟩ := Fin.ext heq
        have heval := dualKnuthTwoOccupiedColoring_of_lt_of_ne hp s t φ
          ⟨p + 1, by omega⟩ (by omega) (by omega)
        rw [hxFin, heval, swapWordColors_eq_some_left_iff hst, hs₁] at hx
        exact hst (Option.some.inj hx)
      omega
    have old_s_prefix (x : Fin n) (hx : x.val < p)
        (hnew : dualKnuthTwoOccupiedColoring hp s t φ x = some s) :
        φ x = some s := by
      rwa [dualKnuthTwoOccupiedColoring_of_le hp s t φ x (by omega)] at hnew
    have old_t_suffix (x : Fin n) (hx : p + 2 < x.val)
        (hnew : dualKnuthTwoOccupiedColoring hp s t φ x = some s) :
        φ x = some t := by
      rw [dualKnuthTwoOccupiedColoring_of_lt_of_ne hp s t φ x
        (by omega) (by omega), swapWordColors_eq_some_left_iff hst] at hnew
      exact hnew
    have prefix_bound_s (x : Fin n) (hx : x.val < p)
        (hnew : dualKnuthTwoOccupiedColoring hp s t φ x = some s) :
        w ⟨p + 2, hp⟩ ≤ w x := by
      have hxφ := old_s_prefix x hx hnew
      have hdec := hφ s x (mem_wordColorBlock.mpr hxφ)
        ⟨p + 1, by omega⟩ (mem_wordColorBlock.mpr hs₁) (by
          change x.val < p + 1
          omega)
      change w (adjacentPositionSwap (p + 1) (by omega)
          ⟨p + 1, by omega⟩) ≤
        w (adjacentPositionSwap (p + 1) (by omega) x) at hdec
      rw [adjacentPositionSwap_left,
        adjacentPositionSwap_apply_of_ne (by omega) x (by omega) (by omega)] at hdec
      exact hdec
    have suffix_bound_s (x : Fin n) (hx : p + 2 < x.val)
        (hnew : dualKnuthTwoOccupiedColoring hp s t φ x = some s) :
        w x ≤ w ⟨p, by omega⟩ := by
      have hxφ := old_t_suffix x hx hnew
      have hdec := hφ t ⟨p, by omega⟩ (mem_wordColorBlock.mpr ht)
        x (mem_wordColorBlock.mpr hxφ) (by
          change p < x.val
          omega)
      change w (adjacentPositionSwap (p + 1) (by omega) x) ≤
        w (adjacentPositionSwap (p + 1) (by omega) ⟨p, by omega⟩) at hdec
      rw [adjacentPositionSwap_apply_of_ne (by omega) x (by omega) (by omega),
        adjacentPositionSwap_apply_of_ne (by omega) _ (by simp) (by
          change p ≠ p + 1 + 1
          omega)] at hdec
      exact hdec
    have prefix_pair_s (x y : Fin n) (hx : x.val < p) (hy : y.val < p)
        (hxy : x < y)
        (hnewx : dualKnuthTwoOccupiedColoring hp s t φ x = some s)
        (hnewy : dualKnuthTwoOccupiedColoring hp s t φ y = some s) :
        w y ≤ w x := by
      have hxφ := old_s_prefix x hx hnewx
      have hyφ := old_s_prefix y hy hnewy
      have hdec := hφ s x (mem_wordColorBlock.mpr hxφ)
        y (mem_wordColorBlock.mpr hyφ) hxy
      change w (adjacentPositionSwap (p + 1) (by omega) y) ≤
        w (adjacentPositionSwap (p + 1) (by omega) x) at hdec
      rw [adjacentPositionSwap_apply_of_ne (by omega) x (by omega) (by omega),
        adjacentPositionSwap_apply_of_ne (by omega) y (by omega) (by omega)] at hdec
      exact hdec
    have suffix_pair_s (x y : Fin n) (hx : p + 2 < x.val)
        (hy : p + 2 < y.val) (hxy : x < y)
        (hnewx : dualKnuthTwoOccupiedColoring hp s t φ x = some s)
        (hnewy : dualKnuthTwoOccupiedColoring hp s t φ y = some s) :
        w y ≤ w x := by
      have hxφ := old_t_suffix x hx hnewx
      have hyφ := old_t_suffix y hy hnewy
      have hdec := hφ t x (mem_wordColorBlock.mpr hxφ)
        y (mem_wordColorBlock.mpr hyφ) hxy
      change w (adjacentPositionSwap (p + 1) (by omega) y) ≤
        w (adjacentPositionSwap (p + 1) (by omega) x) at hdec
      rw [adjacentPositionSwap_apply_of_ne (by omega) x (by omega) (by omega),
        adjacentPositionSwap_apply_of_ne (by omega) y (by omega) (by omega)] at hdec
      exact hdec
    rcases class_s i hi with hip | hiSeam | hiSuf
    · rcases class_s j hj with hjp | hjSeam | hjSuf
      · exact prefix_pair_s i j hip hjp hij hi hj
      · have hjFin : j = ⟨p + 2, hp⟩ := Fin.ext hjSeam
        rw [hjFin]
        exact prefix_bound_s i hip hi
      · exact (suffix_bound_s j hjSuf hj).trans
          ((le_of_lt hbc).trans (prefix_bound_s i hip hi))
    · have hiFin : i = ⟨p + 2, hp⟩ := Fin.ext hiSeam
      rcases class_s j hj with hjp | hjSeam | hjSuf
      · omega
      · omega
      · rw [hiFin]
        exact (suffix_bound_s j hjSuf hj).trans (le_of_lt hbc)
    · rcases class_s j hj with hjp | hjSeam | hjSuf
      · omega
      · omega
      · exact suffix_pair_s i j hiSuf hjSuf hij hi hj
  · by_cases hkt : k = t
    · subst k
      have class_t (x : Fin n)
          (hx : dualKnuthTwoOccupiedColoring hp s t φ x = some t) :
          x.val ≤ p ∨ x.val = p + 1 ∨ p + 2 < x.val := by
        have hxSeam : x.val ≠ p + 2 := by
          intro heq
          have hxFin : x = ⟨p + 2, hp⟩ := Fin.ext heq
          rw [hxFin, dualKnuthTwoOccupiedColoring_seam, hs₂] at hx
          exact hst (Option.some.inj hx)
        omega
      have old_t_prefix (x : Fin n) (hx : x.val ≤ p)
          (hnew : dualKnuthTwoOccupiedColoring hp s t φ x = some t) :
          φ x = some t := by
        rwa [dualKnuthTwoOccupiedColoring_of_le hp s t φ x hx] at hnew
      have old_s_suffix (x : Fin n) (hx : p + 2 < x.val)
          (hnew : dualKnuthTwoOccupiedColoring hp s t φ x = some t) :
          φ x = some s := by
        rw [dualKnuthTwoOccupiedColoring_of_lt_of_ne hp s t φ x
          (by omega) (by omega), swapWordColors_eq_some_right_iff hst] at hnew
        exact hnew
      have prefix_bound_t (x : Fin n) (hx : x.val ≤ p)
          (hnew : dualKnuthTwoOccupiedColoring hp s t φ x = some t) :
          w ⟨p, by omega⟩ ≤ w x := by
        rcases eq_or_lt_of_le hx with heq | hlt
        · have hxFin : x = ⟨p, by omega⟩ := Fin.ext heq
          rw [hxFin]
        · have hxφ := old_t_prefix x hx hnew
          have hdec := hφ t x (mem_wordColorBlock.mpr hxφ)
            ⟨p, by omega⟩ (mem_wordColorBlock.mpr ht) (by
              change x.val < p
              exact hlt)
          change w (adjacentPositionSwap (p + 1) (by omega)
              ⟨p, by omega⟩) ≤
            w (adjacentPositionSwap (p + 1) (by omega) x) at hdec
          rw [adjacentPositionSwap_apply_of_ne (by omega) x (by omega) (by omega),
            adjacentPositionSwap_apply_of_ne (by omega) _ (by simp) (by
              change p ≠ p + 1 + 1
              omega)] at hdec
          exact hdec
      have suffix_bound_t (x : Fin n) (hx : p + 2 < x.val)
          (hnew : dualKnuthTwoOccupiedColoring hp s t φ x = some t) :
          w x ≤ w ⟨p + 1, by omega⟩ := by
        have hxφ := old_s_suffix x hx hnew
        have hdec := hφ s ⟨p + 2, hp⟩ (mem_wordColorBlock.mpr hs₂)
          x (mem_wordColorBlock.mpr hxφ) (by
            change p + 2 < x.val
            exact hx)
        change w (adjacentPositionSwap (p + 1) (by omega) x) ≤
          w (adjacentPositionSwap (p + 1) (by omega) ⟨p + 2, hp⟩) at hdec
        rw [adjacentPositionSwap_right,
          adjacentPositionSwap_apply_of_ne (by omega) x (by omega) (by omega)] at hdec
        exact hdec
      have prefix_pair_t (x y : Fin n) (hx : x.val ≤ p) (hy : y.val ≤ p)
          (hxy : x < y)
          (hnewx : dualKnuthTwoOccupiedColoring hp s t φ x = some t)
          (hnewy : dualKnuthTwoOccupiedColoring hp s t φ y = some t) :
          w y ≤ w x := by
        have hxφ := old_t_prefix x hx hnewx
        have hyφ := old_t_prefix y hy hnewy
        have hdec := hφ t x (mem_wordColorBlock.mpr hxφ)
          y (mem_wordColorBlock.mpr hyφ) hxy
        change w (adjacentPositionSwap (p + 1) (by omega) y) ≤
          w (adjacentPositionSwap (p + 1) (by omega) x) at hdec
        rw [adjacentPositionSwap_apply_of_ne (by omega) x (by omega) (by omega),
          adjacentPositionSwap_apply_of_ne (by omega) y (by omega) (by omega)] at hdec
        exact hdec
      have suffix_pair_t (x y : Fin n) (hx : p + 2 < x.val)
          (hy : p + 2 < y.val) (hxy : x < y)
          (hnewx : dualKnuthTwoOccupiedColoring hp s t φ x = some t)
          (hnewy : dualKnuthTwoOccupiedColoring hp s t φ y = some t) :
          w y ≤ w x := by
        have hxφ := old_s_suffix x hx hnewx
        have hyφ := old_s_suffix y hy hnewy
        have hdec := hφ s x (mem_wordColorBlock.mpr hxφ)
          y (mem_wordColorBlock.mpr hyφ) hxy
        change w (adjacentPositionSwap (p + 1) (by omega) y) ≤
          w (adjacentPositionSwap (p + 1) (by omega) x) at hdec
        rw [adjacentPositionSwap_apply_of_ne (by omega) x (by omega) (by omega),
          adjacentPositionSwap_apply_of_ne (by omega) y (by omega) (by omega)] at hdec
        exact hdec
      rcases class_t i hi with hiPre | hiLocal | hiSuf
      · rcases class_t j hj with hjPre | hjLocal | hjSuf
        · exact prefix_pair_t i j hiPre hjPre hij hi hj
        · have hjFin : j = ⟨p + 1, by omega⟩ := Fin.ext hjLocal
          rw [hjFin]
          exact hab.trans (prefix_bound_t i hiPre hi)
        · exact (suffix_bound_t j hjSuf hj).trans
            (hab.trans (prefix_bound_t i hiPre hi))
      · have hiFin : i = ⟨p + 1, by omega⟩ := Fin.ext hiLocal
        rcases class_t j hj with hjPre | hjLocal | hjSuf
        · omega
        · omega
        · rw [hiFin]
          exact suffix_bound_t j hjSuf hj
      · rcases class_t j hj with hjPre | hjLocal | hjSuf
        · omega
        · omega
        · exact suffix_pair_t i j hiSuf hjSuf hij hi hj
    · have old_other (x : Fin n)
          (hnew : dualKnuthTwoOccupiedColoring hp s t φ x = some k) :
          φ x = some k := by
        by_cases hx : x.val ≤ p
        · rwa [dualKnuthTwoOccupiedColoring_of_le hp s t φ x hx] at hnew
        · by_cases hxSeam : x.val = p + 2
          · have hxFin : x = ⟨p + 2, hp⟩ := Fin.ext hxSeam
            rw [hxFin, dualKnuthTwoOccupiedColoring_seam] at hnew
            rw [hxFin]
            exact hnew
          · rw [dualKnuthTwoOccupiedColoring_of_lt_of_ne hp s t φ x
              (by omega) hxSeam,
            swapWordColors_eq_some_other_iff hks hkt] at hnew
            exact hnew
      have off_triple (x : Fin n)
          (hnew : dualKnuthTwoOccupiedColoring hp s t φ x = some k) :
          x.val ≠ p ∧ x.val ≠ p + 1 ∧ x.val ≠ p + 2 := by
        have hxφ := old_other x hnew
        constructor
        · intro heq
          have hxFin : x = ⟨p, by omega⟩ := Fin.ext heq
          rw [hxFin, ht] at hxφ
          exact hkt (Option.some.inj hxφ).symm
        · constructor
          · intro heq
            have hxFin : x = ⟨p + 1, by omega⟩ := Fin.ext heq
            rw [hxFin, hs₁] at hxφ
            exact hks (Option.some.inj hxφ).symm
          · intro heq
            have hxFin : x = ⟨p + 2, hp⟩ := Fin.ext heq
            rw [hxFin, hs₂] at hxφ
            exact hks (Option.some.inj hxφ).symm
      have hiφ := old_other i hi
      have hjφ := old_other j hj
      have hiOff := off_triple i hi
      have hjOff := off_triple j hj
      have hdec := hφ k i (mem_wordColorBlock.mpr hiφ)
        j (mem_wordColorBlock.mpr hjφ) hij
      change w (adjacentPositionSwap (p + 1) (by omega) j) ≤
        w (adjacentPositionSwap (p + 1) (by omega) i) at hdec
      rw [adjacentPositionSwap_apply_of_ne (by omega) i hiOff.2.1 hiOff.2.2,
        adjacentPositionSwap_apply_of_ne (by omega) j hjOff.2.1 hjOff.2.2] at hdec
      exact hdec

/-- Every support after the dual Knuth move `b a c -> b c a` transports
back to a support of the original word with exactly the same coverage size. -/
theorem exists_dualKnuthTwo_reverse_coloring
    {α : Type*} [LinearOrder α] {n J p : ℕ} (hp : p + 2 < n)
    {w : FiniteWord α n} {φ : WordColoring n J}
    (hab : w ⟨p + 1, by omega⟩ ≤ w ⟨p, by omega⟩)
    (hbc : w ⟨p, by omega⟩ < w ⟨p + 2, hp⟩)
    (hφ : IsWordColoringSupport
      (permuteFiniteWord (adjacentPositionSwap (p + 1) (by omega)) w) φ) :
    ∃ ψ : WordColoring n J,
      IsWordColoringSupport w ψ ∧
        (wordColoringCover ψ).card = (wordColoringCover φ).card := by
  let e := adjacentPositionSwap (p + 1) (by omega : p + 1 + 1 < n)
  by_cases hsame : ∃ s : Fin J,
      φ ⟨p + 1, by omega⟩ = some s ∧ φ ⟨p + 2, hp⟩ = some s
  · obtain ⟨s, hs₁, hs₂⟩ := hsame
    cases ht : φ ⟨p, by omega⟩ with
    | none =>
        refine ⟨dualKnuthTwoVacantColoring hp φ,
          isWordColoringSupport_dualKnuthTwo_vacant hp hab hbc hφ
            hs₁ hs₂ ht, ?_⟩
        exact card_wordColoringCover_dualKnuthTwoVacantColoring hp φ
    | some t =>
        refine ⟨dualKnuthTwoOccupiedColoring hp s t φ,
          isWordColoringSupport_dualKnuthTwo_occupied hp hab hbc hφ
            ht hs₁ hs₂, ?_⟩
        rw [wordColoringCover_dualKnuthTwoOccupiedColoring]
  · have hne : ∀ k : Fin J,
        ¬ (φ ⟨p + 1, by omega⟩ = some k ∧
          φ ⟨p + 2, hp⟩ = some k) := by
      intro k hk
      exact hsame ⟨k, hk⟩
    have htransport := isWordColoringSupport_permute_adjacent_of_ne
      (p := p + 1) (by omega) hφ hne
    have hword : permuteFiniteWord e
        (permuteFiniteWord e w) = w := by
      funext i
      simp [e, permuteFiniteWord, adjacentPositionSwap]
    rw [hword] at htransport
    refine ⟨permuteWordColoring e φ, htransport, ?_⟩
    exact card_wordColoringCover_permute e φ

/-- The coloring Greene maximum is invariant under the dual Knuth move
`b a c <-> b c a` for `a ≤ b < c`. -/
theorem wordColoringGreeneMax_dualKnuthTwo
    {α : Type*} [LinearOrder α] {n p : ℕ} (hp : p + 2 < n)
    (w : FiniteWord α n)
    (hab : w ⟨p + 1, by omega⟩ ≤ w ⟨p, by omega⟩)
    (hbc : w ⟨p, by omega⟩ < w ⟨p + 2, hp⟩) (J : ℕ) :
    wordColoringGreeneMax w J =
      wordColoringGreeneMax
        (permuteFiniteWord (adjacentPositionSwap (p + 1) (by omega)) w) J := by
  let e := adjacentPositionSwap (p + 1) (by omega : p + 1 + 1 < n)
  apply Nat.le_antisymm
  · unfold wordColoringGreeneMax
    apply Finset.sup_le
    intro φ hφ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hφ
    have htransport := isWordColoringSupport_dualKnuthTwo_forward hp
      hab hbc hφ
    rw [← card_wordColoringCover_permute e φ]
    exact Finset.le_sup
      (f := fun ψ : WordColoring n J => (wordColoringCover ψ).card)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htransport⟩)
  · unfold wordColoringGreeneMax
    apply Finset.sup_le
    intro φ hφ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hφ
    obtain ⟨ψ, hψ, hcard⟩ :=
      exists_dualKnuthTwo_reverse_coloring hp hab hbc hφ
    rw [← hcard]
    exact Finset.le_sup
      (f := fun ξ : WordColoring n J => (wordColoringCover ξ).card)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hψ⟩)

/-- Family-form Greene invariance for `b a c <-> b c a`. -/
theorem wordGreeneMax_dualKnuthTwo
    {α : Type*} [LinearOrder α] {n p : ℕ} (hp : p + 2 < n)
    (w : FiniteWord α n)
    (hab : w ⟨p + 1, by omega⟩ ≤ w ⟨p, by omega⟩)
    (hbc : w ⟨p, by omega⟩ < w ⟨p + 2, hp⟩) (J : ℕ) :
    wordGreeneMax w J =
      wordGreeneMax
        (permuteFiniteWord (adjacentPositionSwap (p + 1) (by omega)) w) J := by
  rw [← wordColoringGreeneMax_eq_wordGreeneMax w J,
    wordColoringGreeneMax_dualKnuthTwo hp w hab hbc J,
    wordColoringGreeneMax_eq_wordGreeneMax]

/-! ## Reversal and the second dual Knuth move -/

/-- Reverse the positions of a word and simultaneously dualize its value
order. -/
noncomputable def reverseDualFiniteWord {α : Type*} {n : ℕ} (w : FiniteWord α n) :
    FiniteWord αᵒᵈ n := fun i => w i.rev

/-- Reversing positions and dualizing values transports every coloring
support. -/
theorem isWordColoringSupport_reverseDual
    {α : Type*} [LE α] {n J : ℕ} {w : FiniteWord α n}
    {φ : WordColoring n J} (hφ : IsWordColoringSupport w φ) :
    IsWordColoringSupport (reverseDualFiniteWord w)
      (permuteWordColoring Fin.revPerm φ) := by
  intro k i hi j hj hij
  have hi' : φ i.rev = some k := by
    simpa [permuteWordColoring] using (mem_wordColorBlock.mp hi)
  have hj' : φ j.rev = some k := by
    simpa [permuteWordColoring] using (mem_wordColorBlock.mp hj)
  exact hφ k j.rev (mem_wordColorBlock.mpr hj')
    i.rev (mem_wordColorBlock.mpr hi') (Fin.rev_lt_rev.mpr hij)

@[simp]
theorem reverseDualFiniteWord_reverseDualFiniteWord
    {α : Type*} {n : ℕ} (w : FiniteWord α n) :
    reverseDualFiniteWord (reverseDualFiniteWord w) = w := by
  funext i
  simp [reverseDualFiniteWord] <;> rfl

/-- The coloring Greene maximum is invariant under simultaneous position
reversal and value-order duality. -/
theorem wordColoringGreeneMax_reverseDual
    {α : Type*} [LinearOrder α] {n : ℕ} (w : FiniteWord α n) (J : ℕ) :
    wordColoringGreeneMax (reverseDualFiniteWord w) J =
      wordColoringGreeneMax w J := by
  apply Nat.le_antisymm
  · unfold wordColoringGreeneMax
    apply Finset.sup_le
    intro φ hφ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hφ
    have htransport := isWordColoringSupport_reverseDual hφ
    simp only [reverseDualFiniteWord_reverseDualFiniteWord] at htransport
    rw [← card_wordColoringCover_permute Fin.revPerm φ]
    exact Finset.le_sup
      (f := fun ψ : WordColoring n J => (wordColoringCover ψ).card)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htransport⟩)
  · unfold wordColoringGreeneMax
    apply Finset.sup_le
    intro φ hφ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hφ
    have htransport := isWordColoringSupport_reverseDual hφ
    rw [← card_wordColoringCover_permute Fin.revPerm φ]
    exact Finset.le_sup
      (f := fun ψ : WordColoring n J => (wordColoringCover ψ).card)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htransport⟩)

/-- Family-form reverse-dual Greene invariance. -/
theorem wordGreeneMax_reverseDual
    {α : Type*} [LinearOrder α] {n : ℕ} (w : FiniteWord α n) (J : ℕ) :
    wordGreeneMax (reverseDualFiniteWord w) J = wordGreeneMax w J := by
  rw [← wordColoringGreeneMax_eq_wordGreeneMax,
    wordColoringGreeneMax_reverseDual,
    wordColoringGreeneMax_eq_wordGreeneMax]

private theorem rev_tripleStart {n p : ℕ} (hp : p + 2 < n) :
    (⟨n - (p + 3), by omega⟩ : Fin n).rev = ⟨p + 2, hp⟩ := by
  apply Fin.ext
  simp [Fin.rev]
  omega

private theorem rev_tripleMiddle {n p : ℕ} (hp : p + 2 < n) :
    (⟨n - (p + 3) + 1, by omega⟩ : Fin n).rev =
      ⟨p + 1, by omega⟩ := by
  apply Fin.ext
  simp [Fin.rev]
  omega

private theorem rev_tripleEnd {n p : ℕ} (hp : p + 2 < n) :
    (⟨n - (p + 3) + 2, by omega⟩ : Fin n).rev = ⟨p, by omega⟩ := by
  apply Fin.ext
  simp [Fin.rev]
  omega

/-- Reversal conjugates the swap of the first two positions of a local
triple to the swap of the last two reversed positions. -/
theorem adjacentPositionSwap_rev_triple {n p : ℕ} (hp : p + 2 < n)
    (i : Fin n) :
    adjacentPositionSwap p (by omega) i.rev =
      (adjacentPositionSwap (n - (p + 3) + 1) (by omega) i).rev := by
  unfold adjacentPositionSwap
  rw [Fin.rev_injective.map_swap]
  rw [rev_tripleMiddle hp, rev_tripleEnd hp]
  rw [Equiv.swap_comm]

/-- Word-level form of the reversal conjugation identity. -/
theorem reverseDualFiniteWord_permute_first_two {α : Type*} {n p : ℕ}
    (hp : p + 2 < n) (w : FiniteWord α n) :
    reverseDualFiniteWord
        (permuteFiniteWord (adjacentPositionSwap p (by omega)) w) =
      permuteFiniteWord
        (adjacentPositionSwap (n - (p + 3) + 1) (by omega))
        (reverseDualFiniteWord w) := by
  funext i
  change w (adjacentPositionSwap p (by omega) i.rev) =
    w (adjacentPositionSwap (n - (p + 3) + 1) (by omega) i).rev
  rw [adjacentPositionSwap_rev_triple hp]

/-- Family-form Greene invariance for the second dual Knuth move
`a c b <-> c a b` under `a < b ≤ c`. -/
theorem wordGreeneMax_dualKnuthOne
    {α : Type*} [LinearOrder α] {n p : ℕ} (hp : p + 2 < n)
    (w : FiniteWord α n)
    (hab : w ⟨p, by omega⟩ < w ⟨p + 2, hp⟩)
    (hbc : w ⟨p + 2, hp⟩ ≤ w ⟨p + 1, by omega⟩) (J : ℕ) :
    wordGreeneMax w J =
      wordGreeneMax
        (permuteFiniteWord (adjacentPositionSwap p (by omega)) w) J := by
  let q := n - (p + 3)
  let rw : FiniteWord αᵒᵈ n := reverseDualFiniteWord w
  have hq : q + 2 < n := by
    dsimp only [q]
    omega
  have h₁ : rw ⟨q + 1, by omega⟩ ≤ rw ⟨q, by omega⟩ := by
    change w (⟨q, by omega⟩ : Fin n).rev ≤
      w (⟨q + 1, by omega⟩ : Fin n).rev
    dsimp only [q]
    rw [rev_tripleStart hp, rev_tripleMiddle hp]
    exact hbc
  have h₂ : rw ⟨q, by omega⟩ < rw ⟨q + 2, hq⟩ := by
    change w (⟨q + 2, hq⟩ : Fin n).rev <
      w (⟨q, by omega⟩ : Fin n).rev
    dsimp only [q]
    rw [rev_tripleEnd hp, rev_tripleStart hp]
    exact hab
  let target := permuteFiniteWord (adjacentPositionSwap p (by omega)) w
  calc
    wordGreeneMax w J = wordGreeneMax rw J :=
      (wordGreeneMax_reverseDual w J).symm
    _ = wordGreeneMax
        (permuteFiniteWord (adjacentPositionSwap (q + 1) (by omega)) rw) J :=
      wordGreeneMax_dualKnuthTwo hq rw h₁ h₂ J
    _ = wordGreeneMax (reverseDualFiniteWord target) J := by
      congr 2
      dsimp only [target, rw, q]
      exact (reverseDualFiniteWord_permute_first_two hp w).symm
    _ = wordGreeneMax target J := wordGreeneMax_reverseDual target J

end Multisegment

end


/- SOURCE Multisegment/Greene/DualPlactic.lean -/
section
/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI-generated by Elazar Gershuni
-/

/-!
# The dual plactic equivalence of finite words

This file packages the two local dual Knuth moves proved in
`Multisegment.Greene.Word` into their reflexive, symmetric, transitive
closure.  The weakly decreasing Greene maxima are consequently invariants
of the resulting dual plactic class.

Keeping the relation on fixed-length function words avoids list-length casts
in later insertion arguments.  A move may occur at any adjacent triple, so
the surrounding word context is already built into the definition.
-/

namespace Multisegment

/-- Dual plactic equivalence, generated by the two dual Knuth moves
`a c b <-> c a b` for `a < b <= c` and
`b a c <-> b c a` for `a <= b < c`. -/
inductive DualPlacticEq {α : Type*} [LinearOrder α] {n : ℕ} :
    FiniteWord α n → FiniteWord α n → Prop
  | refl (w : FiniteWord α n) : DualPlacticEq w w
  | knuthOne (w : FiniteWord α n) (p : ℕ) (hp : p + 2 < n)
      (hab : w ⟨p, by omega⟩ < w ⟨p + 2, hp⟩)
      (hbc : w ⟨p + 2, hp⟩ ≤ w ⟨p + 1, by omega⟩) :
      DualPlacticEq w
        (permuteFiniteWord (adjacentPositionSwap p (by omega)) w)
  | knuthTwo (w : FiniteWord α n) (p : ℕ) (hp : p + 2 < n)
      (hab : w ⟨p + 1, by omega⟩ ≤ w ⟨p, by omega⟩)
      (hbc : w ⟨p, by omega⟩ < w ⟨p + 2, hp⟩) :
      DualPlacticEq w
        (permuteFiniteWord (adjacentPositionSwap (p + 1) (by omega)) w)
  | symm {u v : FiniteWord α n} :
      DualPlacticEq u v → DualPlacticEq v u
  | trans {u v w : FiniteWord α n} :
      DualPlacticEq u v → DualPlacticEq v w → DualPlacticEq u w

/-- Every finite-budget weakly decreasing Greene maximum is constant on a
dual plactic class. -/
theorem wordGreeneMax_eq_of_dualPlacticEq
    {α : Type*} [LinearOrder α] {n : ℕ}
    {u v : FiniteWord α n} (h : DualPlacticEq u v) (J : ℕ) :
    wordGreeneMax u J = wordGreeneMax v J := by
  induction h with
  | refl => rfl
  | knuthOne w p hp hab hbc =>
      exact wordGreeneMax_dualKnuthOne hp w hab hbc J
  | knuthTwo w p hp hab hbc =>
      exact wordGreeneMax_dualKnuthTwo hp w hab hbc J
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## List presentation -/

/-- List presentation of dual plactic equivalence.  The left and right
contexts in each generating move make congruence under concatenation
explicit without adding separate quotient machinery. -/
inductive ListDualPlacticEq {α : Type*} [LinearOrder α] :
    List α → List α → Prop
  | refl (w : List α) : ListDualPlacticEq w w
  | knuthOne (left right : List α) (a b c : α)
      (hab : a < b) (hbc : b ≤ c) :
      ListDualPlacticEq
        (left ++ [a, c, b] ++ right)
        (left ++ [c, a, b] ++ right)
  | knuthTwo (left right : List α) (a b c : α)
      (hab : a ≤ b) (hbc : b < c) :
      ListDualPlacticEq
        (left ++ [b, a, c] ++ right)
        (left ++ [b, c, a] ++ right)
  | symm {u v : List α} :
      ListDualPlacticEq u v → ListDualPlacticEq v u
  | trans {u v w : List α} :
      ListDualPlacticEq u v → ListDualPlacticEq v w →
        ListDualPlacticEq u w

/-- Dual plactic equivalence is stable under a common left context. -/
theorem ListDualPlacticEq.append_left
    {α : Type*} [LinearOrder α] {u v : List α}
    (h : ListDualPlacticEq u v) (pre : List α) :
    ListDualPlacticEq (pre ++ u) (pre ++ v) := by
  induction h with
  | refl w => exact ListDualPlacticEq.refl _
  | knuthOne left right a b c hab hbc =>
      simpa only [List.append_assoc] using
        ListDualPlacticEq.knuthOne (pre ++ left) right a b c hab hbc
  | knuthTwo left right a b c hab hbc =>
      simpa only [List.append_assoc] using
        ListDualPlacticEq.knuthTwo (pre ++ left) right a b c hab hbc
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Dual plactic equivalence is stable under a common right context. -/
theorem ListDualPlacticEq.append_right
    {α : Type*} [LinearOrder α] {u v : List α}
    (h : ListDualPlacticEq u v) (post : List α) :
    ListDualPlacticEq (u ++ post) (v ++ post) := by
  induction h with
  | refl w => exact ListDualPlacticEq.refl _
  | knuthOne left right a b c hab hbc =>
      simpa only [List.append_assoc] using
        ListDualPlacticEq.knuthOne left (right ++ post) a b c hab hbc
  | knuthTwo left right a b c hab hbc =>
      simpa only [List.append_assoc] using
        ListDualPlacticEq.knuthTwo left (right ++ post) a b c hab hbc
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A letter weakly above the end of a strict row can be moved to the
front while retaining that row. -/
theorem listDualPlacticEq_bump_front
    {α : Type*} [LinearOrder α] (row : List α) (b x : α)
    (hrow : (row ++ [x]).Pairwise (fun a b => a < b)) (hxb : x ≤ b) :
    ListDualPlacticEq ((row ++ [b]) ++ [x]) (b :: row ++ [x]) := by
  induction row using List.reverseRecOn generalizing b x with
  | nil =>
      simpa using (ListDualPlacticEq.refl [b, x])
  | append_singleton row y ih =>
      rw [List.pairwise_append] at hrow
      have hprefix : (row ++ [y]).Pairwise (fun a b => a < b) := hrow.1
      have hyx : y < x := hrow.2.2 y (by simp) x (by simp)
      have hyb : y ≤ b := (hyx.trans_le hxb).le
      have hstep :=
        ListDualPlacticEq.knuthOne row [] y x b hyx hxb
      have hmove := (ih b y hprefix hyb).append_right [x]
      have hstep' :
          ListDualPlacticEq
            (((row ++ [y]) ++ [b]) ++ [x])
            (((row ++ [b]) ++ [y]) ++ [x]) := by
        simpa [List.append_assoc] using hstep
      have hmove' :
          ListDualPlacticEq
            (((row ++ [b]) ++ [y]) ++ [x])
            ((b :: row ++ [y]) ++ [x]) := by
        simpa [List.append_assoc] using hmove
      exact hstep'.trans hmove'

/-- A letter weakly below the head of a strict row can be moved immediately
after that head. -/
theorem listDualPlacticEq_bump_after_head
    {α : Type*} [LinearOrder α] (head : α) (row : List α) (x : α)
    (hrow : (head :: row).Pairwise (fun a b => a < b))
    (hxh : x ≤ head) :
    ListDualPlacticEq (head :: row ++ [x]) (head :: x :: row) := by
  induction row generalizing head x with
  | nil =>
      simpa using (ListDualPlacticEq.refl [head, x])
  | cons y row ih =>
      rw [List.pairwise_cons] at hrow
      have hhy : head < y := hrow.1 y (by simp)
      have hxy : x ≤ y := hxh.trans hhy.le
      have hmove := (ih y x hrow.2 hxy).append_left [head]
      have hstep :=
        (ListDualPlacticEq.knuthTwo [] row x head y hxh hhy).symm
      have hmove' :
          ListDualPlacticEq
            (head :: y :: row ++ [x])
            (head :: y :: x :: row) := by
        simpa [List.append_assoc] using hmove
      have hstep' :
          ListDualPlacticEq
            (head :: y :: x :: row)
            (head :: x :: y :: row) := by
        simpa [List.append_assoc] using hstep
      exact hmove'.trans hstep'

/-! ## Dual row insertion -/

/-- Insert a letter into one strictly increasing row.  The first entry
weakly above the new letter is replaced and returned as the bump; if no such
entry exists, the letter is appended and no bump is returned. -/
noncomputable def dualRowBump {α : Type*} [LinearOrder α] :
    List α → α → Option α × List α
  | [], x => (none, [x])
  | y :: row, x =>
      if x ≤ y then (some y, x :: row)
      else
        let result := dualRowBump row x
        (result.1, y :: result.2)

/-- If dual row insertion returns no bump, it simply appended the new
letter. -/
theorem dualRowBump_snd_of_fst_eq_none
    {α : Type*} [LinearOrder α] (row : List α) (x : α)
    (h : (dualRowBump row x).1 = none) :
    (dualRowBump row x).2 = row ++ [x] := by
  induction row with
  | nil => simp [dualRowBump]
  | cons y row ih =>
      by_cases hxy : x ≤ y
      · simp [dualRowBump, hxy] at h
      · have htail : (dualRowBump row x).1 = none := by
          simpa [dualRowBump, hxy] using h
        simp [dualRowBump, hxy, ih htail]

/-- A returned bump identifies the first row entry weakly above the new
letter, together with the unchanged prefix and suffix. -/
theorem dualRowBump_eq_some_spec
    {α : Type*} [LinearOrder α] (row : List α) (x b : α)
    (h : (dualRowBump row x).1 = some b) :
    ∃ left right : List α,
      row = left ++ b :: right ∧
      (dualRowBump row x).2 = left ++ x :: right ∧
      (∀ y ∈ left, y < x) ∧ x ≤ b := by
  induction row with
  | nil => simp [dualRowBump] at h
  | cons y row ih =>
      by_cases hxy : x ≤ y
      · have hyb : y = b := by
          have hs : some y = some b := by
            simpa [dualRowBump, hxy] using h
          exact Option.some.inj hs
        subst b
        exact ⟨[], row, by simp, by simp [dualRowBump, hxy], by simp, hxy⟩
      · have htail : (dualRowBump row x).1 = some b := by
          simpa [dualRowBump, hxy] using h
        obtain ⟨left, right, hrow, hnew, hleft, hxb⟩ := ih htail
        refine ⟨y :: left, right, ?_, ?_, ?_, hxb⟩
        · simp [hrow]
        · simp [dualRowBump, hxy, hnew]
        · intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact lt_of_not_ge hxy
          · exact hleft z hz

/-- One dual row insertion is dual-plactic equivalent to appending the
inserted letter.  A returned bump is placed immediately before the edited
row, matching bottom-to-top tableau reading. -/
theorem listDualPlacticEq_dualRowBump
    {α : Type*} [LinearOrder α] (row : List α) (x : α)
    (hrow : row.Pairwise (fun a b => a < b)) :
    let result := dualRowBump row x
    ListDualPlacticEq (row ++ [x]) (result.1.toList ++ result.2) := by
  dsimp only
  cases hbump : (dualRowBump row x).1 with
  | none =>
      have hnew := dualRowBump_snd_of_fst_eq_none row x hbump
      rw [hnew]
      simpa using (ListDualPlacticEq.refl (row ++ [x]))
  | some b =>
      obtain ⟨left, right, hrowEq, hnew, hleft, hxb⟩ :=
        dualRowBump_eq_some_spec row x b hbump
      rw [hrowEq, List.pairwise_append] at hrow
      have hleftX :
          (left ++ [x]).Pairwise (fun a b => a < b) := by
        rw [List.pairwise_append]
        refine ⟨hrow.1, by simp, ?_⟩
        intro y hy z hz
        simp only [List.mem_singleton] at hz
        subst z
        exact hleft y hy
      have hstep₁ :=
        (listDualPlacticEq_bump_after_head b right x hrow.2.1 hxb).append_left left
      have hstep₂ :=
        (listDualPlacticEq_bump_front left b x hleftX hxb).append_right right
      have hstep₁' :
          ListDualPlacticEq
            ((left ++ b :: right) ++ [x])
            (left ++ b :: x :: right) := by
        simpa [List.append_assoc] using hstep₁
      have hstep₂' :
          ListDualPlacticEq
            (left ++ b :: x :: right)
            (b :: left ++ x :: right) := by
        simpa [List.append_assoc] using hstep₂
      rw [hnew, hrowEq]
      simpa [List.append_assoc] using hstep₁'.trans hstep₂'

/-- Insert a letter through successive rows using `dualRowBump`. -/
noncomputable def dualTableauInsert {α : Type*} [LinearOrder α] :
    List (List α) → α → List (List α)
  | [], x => [[x]]
  | row :: rows, x =>
      let result := dualRowBump row x
      result.2 :: match result.1 with
        | none => rows
        | some bumped => dualTableauInsert rows bumped

/-- Bottom-to-top, left-to-right row reading of a raw tableau. -/
noncomputable def dualTableauWord {α : Type*} (rows : List (List α)) : List α :=
  rows.reverse.flatten

@[simp]
theorem dualTableauWord_cons {α : Type*} (row : List α)
    (rows : List (List α)) :
    dualTableauWord (row :: rows) = dualTableauWord rows ++ row := by
  simp [dualTableauWord]

/-- Inserting one letter into strict rows gives the dual-plactic normal
form of appending that letter to the tableau reading word. -/
theorem listDualPlacticEq_dualTableauInsert
    {α : Type*} [LinearOrder α] (rows : List (List α)) (x : α)
    (hrows : ∀ row ∈ rows, row.Pairwise (fun a b => a < b)) :
    ListDualPlacticEq (dualTableauWord rows ++ [x])
      (dualTableauWord (dualTableauInsert rows x)) := by
  induction rows generalizing x with
  | nil =>
      simpa [dualTableauWord, dualTableauInsert] using
        (ListDualPlacticEq.refl [x])
  | cons row rows ih =>
      have hrow := hrows row (by simp)
      have htail : ∀ r ∈ rows, r.Pairwise (fun a b => a < b) := by
        intro r hr
        exact hrows r (by simp [hr])
      have hrowMove := listDualPlacticEq_dualRowBump row x hrow
      cases hbump : (dualRowBump row x).1 with
      | none =>
          have hnew := dualRowBump_snd_of_fst_eq_none row x hbump
          have hmove := hrowMove.append_left (dualTableauWord rows)
          simpa [dualTableauInsert, hbump, hnew, List.append_assoc] using hmove
      | some bumped =>
          have hmove := hrowMove.append_left (dualTableauWord rows)
          have hrec := (ih bumped htail).append_right (dualRowBump row x).2
          have hmove' :
              ListDualPlacticEq
                ((dualTableauWord rows ++ row) ++ [x])
                ((dualTableauWord rows ++ [bumped]) ++
                  (dualRowBump row x).2) := by
            simpa [hbump, List.append_assoc] using hmove
          simpa [dualTableauInsert, hbump, List.append_assoc] using
            hmove'.trans hrec

/-- Every entry in an edited row is either the inserted letter or an entry
of the original row. -/
theorem mem_dualRowBump_snd
    {α : Type*} [LinearOrder α] (row : List α) (x z : α)
    (hz : z ∈ (dualRowBump row x).2) :
    z = x ∨ z ∈ row := by
  induction row with
  | nil => simpa [dualRowBump] using hz
  | cons y row ih =>
      by_cases hxy : x ≤ y
      · simp only [dualRowBump, hxy, ↓reduceIte, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact Or.inl rfl
        · exact Or.inr (by simp [hz])
      · simp only [dualRowBump, hxy, ↓reduceIte, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact Or.inr (by simp)
        · rcases ih hz with rfl | hz
          · exact Or.inl rfl
          · exact Or.inr (by simp [hz])

/-- Dual row insertion preserves strict increase along the edited row. -/
theorem dualRowBump_snd_pairwise
    {α : Type*} [LinearOrder α] (row : List α) (x : α)
    (hrow : row.Pairwise (fun a b => a < b)) :
    (dualRowBump row x).2.Pairwise (fun a b => a < b) := by
  induction row generalizing x with
  | nil => simp [dualRowBump]
  | cons y row ih =>
      rw [List.pairwise_cons] at hrow
      by_cases hxy : x ≤ y
      · simp only [dualRowBump, hxy, ↓reduceIte, List.pairwise_cons]
        exact ⟨fun z hz => hxy.trans_lt (hrow.1 z hz), hrow.2⟩
      · simp only [dualRowBump, hxy, ↓reduceIte, List.pairwise_cons]
        refine ⟨?_, ih x hrow.2⟩
        intro z hz
        rcases mem_dualRowBump_snd row x z hz with rfl | hz
        · exact lt_of_not_ge hxy
        · exact hrow.1 z hz

/-- If all input rows are strict, every row remains strict after inserting
one letter. -/
theorem dualTableauInsert_rows_pairwise
    {α : Type*} [LinearOrder α] (rows : List (List α)) (x : α)
    (hrows : ∀ row ∈ rows, row.Pairwise (fun a b => a < b)) :
    ∀ row ∈ dualTableauInsert rows x,
      row.Pairwise (fun a b => a < b) := by
  induction rows generalizing x with
  | nil =>
      intro row hrow
      simp only [dualTableauInsert, List.mem_cons, List.not_mem_nil,
        or_false] at hrow
      subst row
      simp
  | cons first rows ih =>
      have hfirst := hrows first (by simp)
      have htail : ∀ row ∈ rows,
          row.Pairwise (fun a b => a < b) := by
        intro row hrow
        exact hrows row (by simp [hrow])
      intro row hrow
      simp only [dualTableauInsert, List.mem_cons] at hrow
      rcases hrow with hrow | hrow
      · subst row
        exact dualRowBump_snd_pairwise first x hfirst
      · cases hbump : (dualRowBump first x).1 with
        | none =>
            simpa [hbump] using htail row (by simpa [hbump] using hrow)
        | some bumped =>
            exact ih bumped htail row (by simpa [hbump] using hrow)

/-- Dual insertion tableau rows of a word, built from left to right. -/
noncomputable def dualInsertionRows {α : Type*} [LinearOrder α] (word : List α) :
    List (List α) :=
  word.foldl dualTableauInsert []

/-- Every row of the dual insertion tableau is strictly increasing. -/
theorem dualInsertionRows_pairwise
    {α : Type*} [LinearOrder α] (word : List α) :
    ∀ row ∈ dualInsertionRows word,
      row.Pairwise (fun a b => a < b) := by
  induction word using List.reverseRecOn with
  | nil => simp [dualInsertionRows]
  | append_singleton word x ih =>
      rw [dualInsertionRows, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact dualTableauInsert_rows_pairwise (dualInsertionRows word) x ih

/-- Every word is dual-plactic equivalent to the bottom-to-top row reading
of its dual insertion tableau. -/
theorem listDualPlacticEq_dualInsertionRows
    {α : Type*} [LinearOrder α] (word : List α) :
    ListDualPlacticEq word
      (dualTableauWord (dualInsertionRows word)) := by
  induction word using List.reverseRecOn with
  | nil =>
      simpa [dualInsertionRows, dualTableauWord] using
        (ListDualPlacticEq.refl ([] : List α))
  | append_singleton word x ih =>
      have hprefix := ih.append_right [x]
      have hinsert := listDualPlacticEq_dualTableauInsert
        (dualInsertionRows word) x (dualInsertionRows_pairwise word)
      have hnormal := hprefix.trans hinsert
      simpa [dualInsertionRows, List.foldl_append] using hnormal

/-! ## Greene invariance of list words -/

/-- Weakly decreasing Greene maximum of a list word. -/
noncomputable def listWordGreeneMax {α : Type*} [LE α]
    [DecidableRel (fun x y : α => x ≤ y)]
    (word : List α) (J : ℕ) : ℕ :=
  wordGreeneMax word.get J

/-- A fixed-length word agrees with the list Greene statistic when it is
pointwise the list word after transporting the length equality. -/
theorem wordGreeneMax_eq_listWordGreeneMax_of_get
    {α : Type*} [LE α] [DecidableRel (fun x y : α => x ≤ y)]
    {n : ℕ} (w : FiniteWord α n) (word : List α)
    (hlen : word.length = n)
    (hget : ∀ i : Fin n, w i = word.get (Fin.cast hlen.symm i)) (J : ℕ) :
    wordGreeneMax w J = listWordGreeneMax word J := by
  subst n
  have hw : w = word.get := funext fun i => by simpa using hget i
  rw [hw]
  rfl

/-- Swapping the first two letters after a list prefix is exactly the
corresponding adjacent permutation of the fixed-length list word. -/
theorem permuteFiniteWord_get_swap_context
    {α : Type*} (pre post : List α) (x y : α) :
    let source := pre ++ (x :: y :: post)
    let target := pre ++ (y :: x :: post)
    let hlen : target.length = source.length := by
      simp [target, source]
    ∀ i : Fin source.length,
      (permuteFiniteWord
          (adjacentPositionSwap pre.length (by simp [source]))
          source.get) i =
        target.get (Fin.cast hlen.symm i) := by
  dsimp only
  intro i
  by_cases hi₀ : i.val = pre.length
  · have hi : i = ⟨pre.length, by simp⟩ := Fin.ext hi₀
    subst i
    simp only [permuteFiniteWord, Function.comp_apply]
    rw [adjacentPositionSwap_left]
    simp [List.get_eq_getElem]
  · by_cases hi₁ : i.val = pre.length + 1
    · have hi : i = ⟨pre.length + 1, by simp⟩ := Fin.ext hi₁
      subst i
      simp only [permuteFiniteWord, Function.comp_apply]
      rw [adjacentPositionSwap_right]
      simp [List.get_eq_getElem]
    · have hswap := adjacentPositionSwap_apply_of_ne
          (n := (pre ++ (x :: y :: post)).length)
          (p := pre.length) (by simp) i hi₀ hi₁
      simp only [permuteFiniteWord, Function.comp_apply]
      rw [hswap]
      have hopt : (pre ++ (x :: y :: post))[i.val]? =
          (pre ++ (y :: x :: post))[i.val]? := by
        by_cases hlt : i.val < pre.length
        · simp [List.getElem?_append, hlt]
        · have hge : pre.length + 2 ≤ i.val := by omega
          simp only [List.getElem?_append, hlt, ↓reduceIte]
          rw [show i.val - pre.length =
            (i.val - pre.length - 2) + 2 by omega]
          simp
      simp only [List.get_eq_getElem]
      apply Option.some.inj
      rw [← List.getElem?_eq_getElem i.isLt]
      rw [← List.getElem?_eq_getElem (Fin.cast (by simp) i).isLt]
      exact hopt

/-- The first dual Knuth move preserves the list-word Greene maximum in an
arbitrary context. -/
theorem listWordGreeneMax_knuthOne
    {α : Type*} [LinearOrder α] (left right : List α) (a b c : α)
    (hab : a < b) (hbc : b ≤ c) (J : ℕ) :
    listWordGreeneMax (left ++ (a :: c :: b :: right)) J =
      listWordGreeneMax (left ++ (c :: a :: b :: right)) J := by
  let source := left ++ (a :: c :: b :: right)
  let target := left ++ (c :: a :: b :: right)
  let w : FiniteWord α source.length := source.get
  have hp : left.length + 2 < source.length := by
    simp [source]
  have h₁ : w ⟨left.length, by omega⟩ <
      w ⟨left.length + 2, hp⟩ := by
    simp [w, source]
    exact hab
  have h₂ : w ⟨left.length + 2, hp⟩ ≤
      w ⟨left.length + 1, by omega⟩ := by
    simp [w, source]
    exact hbc
  have hmove := wordGreeneMax_dualKnuthOne hp w h₁ h₂ J
  have hlen : target.length = source.length := by
    simp [target, source]
  have hget : ∀ i : Fin source.length,
      (permuteFiniteWord
        (adjacentPositionSwap left.length (by omega)) w) i =
        target.get (Fin.cast hlen.symm i) := by
    simpa [w, source, target] using
      permuteFiniteWord_get_swap_context left (b :: right) a c
  calc
    listWordGreeneMax (left ++ (a :: c :: b :: right)) J =
        wordGreeneMax w J := rfl
    _ = wordGreeneMax
        (permuteFiniteWord
          (adjacentPositionSwap left.length (by omega)) w) J := hmove
    _ = listWordGreeneMax target J :=
      wordGreeneMax_eq_listWordGreeneMax_of_get _ target hlen hget J
    _ = listWordGreeneMax (left ++ (c :: a :: b :: right)) J := rfl

/-- The second dual Knuth move preserves the list-word Greene maximum in an
arbitrary context. -/
theorem listWordGreeneMax_knuthTwo
    {α : Type*} [LinearOrder α] (left right : List α) (a b c : α)
    (hab : a ≤ b) (hbc : b < c) (J : ℕ) :
    listWordGreeneMax ((left ++ [b]) ++ (a :: c :: right)) J =
      listWordGreeneMax ((left ++ [b]) ++ (c :: a :: right)) J := by
  let source := (left ++ [b]) ++ (a :: c :: right)
  let target := (left ++ [b]) ++ (c :: a :: right)
  let w : FiniteWord α source.length := source.get
  have hp : left.length + 2 < source.length := by
    simp [source]
  have h₁ : w ⟨left.length + 1, by omega⟩ ≤
      w ⟨left.length, by omega⟩ := by
    simp [w, source]
    exact hab
  have h₂ : w ⟨left.length, by omega⟩ <
      w ⟨left.length + 2, hp⟩ := by
    simp [w, source]
    exact hbc
  have hmove := wordGreeneMax_dualKnuthTwo hp w h₁ h₂ J
  have hlen : target.length = source.length := by
    simp [target, source]
  have hget : ∀ i : Fin source.length,
      (permuteFiniteWord
        (adjacentPositionSwap (left.length + 1) (by omega)) w) i =
        target.get (Fin.cast hlen.symm i) := by
    simpa [w, source, target] using
      permuteFiniteWord_get_swap_context (left ++ [b]) right a c
  calc
    listWordGreeneMax ((left ++ [b]) ++ (a :: c :: right)) J =
        wordGreeneMax w J := rfl
    _ = wordGreeneMax
        (permuteFiniteWord
          (adjacentPositionSwap (left.length + 1) (by omega)) w) J := hmove
    _ = listWordGreeneMax target J :=
      wordGreeneMax_eq_listWordGreeneMax_of_get _ target hlen hget J
    _ = listWordGreeneMax ((left ++ [b]) ++ (c :: a :: right)) J := rfl

/-- The list-word Greene maximum is constant on every dual plactic class. -/
theorem listWordGreeneMax_eq_of_listDualPlacticEq
    {α : Type*} [LinearOrder α] {u v : List α}
    (h : ListDualPlacticEq u v) (J : ℕ) :
    listWordGreeneMax u J = listWordGreeneMax v J := by
  induction h with
  | refl => rfl
  | knuthOne left right a b c hab hbc =>
      simpa [List.append_assoc] using
        listWordGreeneMax_knuthOne left right a b c hab hbc J
  | knuthTwo left right a b c hab hbc =>
      simpa [List.append_assoc] using
        listWordGreeneMax_knuthTwo left right a b c hab hbc J
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A word and the row reading of its dual insertion tableau have the same
weakly decreasing Greene maxima. -/
theorem listWordGreeneMax_dualInsertionRows
    {α : Type*} [LinearOrder α] (word : List α) (J : ℕ) :
    listWordGreeneMax word J =
      listWordGreeneMax
        (dualTableauWord (dualInsertionRows word)) J :=
  listWordGreeneMax_eq_of_listDualPlacticEq
    (listDualPlacticEq_dualInsertionRows word) J

/-! ## Tableau interlacing -/

/-- An upper row dominates a lower row when the lower row is no longer and
entries weakly increase down every represented column. -/
noncomputable def DualRowDominates {α : Type*} [LE α] : List α → List α → Prop
  | _, [] => True
  | [], _ :: _ => False
  | upper :: uppers, lower :: lowers =>
      upper ≤ lower ∧ DualRowDominates uppers lowers

/-- Editing an upper row by dual insertion preserves every existing
columnwise dominance relation below it. -/
theorem DualRowDominates.dualRowBump_left
    {α : Type*} [LinearOrder α] {upper lower : List α} (x : α)
    (hdom : DualRowDominates upper lower) :
    DualRowDominates (dualRowBump upper x).2 lower := by
  induction upper generalizing lower with
  | nil =>
      cases lower with
      | nil => simp [dualRowBump, DualRowDominates]
      | cons lower lowers => simp [DualRowDominates] at hdom
  | cons u upper ih =>
      cases lower with
      | nil => simp [DualRowDominates]
      | cons l lower =>
          simp only [DualRowDominates] at hdom ⊢
          by_cases hxu : x ≤ u
          · simpa [dualRowBump, hxu, DualRowDominates] using
              And.intro (hxu.trans hdom.1) hdom.2
          · simpa [dualRowBump, hxu, DualRowDominates] using
              And.intro hdom.1 (ih hdom.2)

/-- Passing a bump from an upper strict row into a dominated lower row
preserves columnwise dominance between the edited rows. -/
theorem dualRowBump_preserves_dominance
    {α : Type*} [LinearOrder α] (upper lower : List α) (x : α)
    (hupper : upper.Pairwise (fun a b => a < b))
    (hdom : DualRowDominates upper lower) :
    let result := dualRowBump upper x
    DualRowDominates result.2
      (match result.1 with
        | none => lower
        | some bumped => (dualRowBump lower bumped).2) := by
  induction upper generalizing lower x with
  | nil =>
      cases lower with
      | nil => simp [dualRowBump, DualRowDominates]
      | cons lower lowers => simp [DualRowDominates] at hdom
  | cons u upper ih =>
      rw [List.pairwise_cons] at hupper
      cases lower with
      | nil =>
          by_cases hxu : x ≤ u
          · simp [dualRowBump, hxu, DualRowDominates]
          · cases hbump : (dualRowBump upper x).1 with
            | none => simp [dualRowBump, hxu, hbump, DualRowDominates]
            | some bumped =>
                obtain ⟨left, right, hrow, -, -, -⟩ :=
                  dualRowBump_eq_some_spec upper x bumped hbump
                have hub : u ≤ bumped := by
                  exact (hupper.1 bumped (by simp [hrow])).le
                simp [dualRowBump, hxu, hbump, DualRowDominates, hub]
      | cons l lower =>
          simp only [DualRowDominates] at hdom
          by_cases hxu : x ≤ u
          · have hul : u ≤ l := hdom.1
            simpa [dualRowBump, hxu, hul, DualRowDominates] using
              And.intro hxu hdom.2
          · cases hbump : (dualRowBump upper x).1 with
            | none =>
                have htail := hdom.2.dualRowBump_left x
                simpa [dualRowBump, hxu, hbump, DualRowDominates] using
                  And.intro hdom.1 htail
            | some bumped =>
                obtain ⟨left, right, hrow, -, -, -⟩ :=
                  dualRowBump_eq_some_spec upper x bumped hbump
                have hub : u ≤ bumped := by
                  exact (hupper.1 bumped (by simp [hrow])).le
                by_cases hbl : bumped ≤ l
                · have htail := hdom.2.dualRowBump_left x
                  simpa [dualRowBump, hxu, hbump, hbl,
                    DualRowDominates] using And.intro hub htail
                · have htail := ih lower x hupper.2 hdom.2
                  simpa [dualRowBump, hxu, hbump, hbl,
                    DualRowDominates] using And.intro hdom.1 htail

/-- Raw dual tableaux: every row is strict and each row dominates the next
one in the weak-column order. -/
noncomputable def IsDualTableauRows {α : Type*} [LT α] [LE α] :
    List (List α) → Prop
  | [] => True
  | row :: rows =>
      row.Pairwise (fun a b => a < b) ∧
        match rows with
        | [] => True
        | next :: _ =>
            DualRowDominates row next ∧ IsDualTableauRows rows

/-- Dual insertion preserves strict rows and weak column interlacing. -/
theorem isDualTableauRows_dualTableauInsert
    {α : Type*} [LinearOrder α] (rows : List (List α)) (x : α)
    (hrows : IsDualTableauRows rows) :
    IsDualTableauRows (dualTableauInsert rows x) := by
  induction rows generalizing x with
  | nil => simp [dualTableauInsert, IsDualTableauRows]
  | cons first rows ih =>
      cases rows with
      | nil =>
          have hfirst : first.Pairwise (fun a b => a < b) := by
            simpa [IsDualTableauRows] using hrows
          have hnew := dualRowBump_snd_pairwise first x hfirst
          cases hbump : (dualRowBump first x).1 with
          | none =>
              simpa [dualTableauInsert, hbump, IsDualTableauRows] using hnew
          | some bumped =>
              have hdom :=
                dualRowBump_preserves_dominance first [] x hfirst (by
                  simp [DualRowDominates])
              simp only [hbump] at hdom
              simp [dualRowBump] at hdom
              simpa [dualTableauInsert, hbump, IsDualTableauRows] using
                And.intro hnew (And.intro hdom trivial)
      | cons second rows =>
          simp only [IsDualTableauRows] at hrows
          have hfirst := hrows.1
          have hdom := hrows.2.1
          have htail := hrows.2.2
          have hnew := dualRowBump_snd_pairwise first x hfirst
          cases hbump : (dualRowBump first x).1 with
          | none =>
              have hnewDom := hdom.dualRowBump_left x
              simpa [dualTableauInsert, hbump, IsDualTableauRows] using
                And.intro hnew (And.intro hnewDom htail)
          | some bumped =>
              have hnewDom :=
                dualRowBump_preserves_dominance first second x hfirst hdom
              simp only [hbump] at hnewDom
              have htailNew := ih bumped htail
              simpa [dualTableauInsert, hbump, IsDualTableauRows] using
                And.intro hnew (And.intro hnewDom htailNew)

/-- The rows produced by dual insertion form a row-strict,
column-weak tableau. -/
theorem isDualTableauRows_dualInsertionRows
    {α : Type*} [LinearOrder α] (word : List α) :
    IsDualTableauRows (dualInsertionRows word) := by
  induction word using List.reverseRecOn with
  | nil => simp [dualInsertionRows, IsDualTableauRows]
  | append_singleton word x ih =>
      rw [dualInsertionRows, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact isDualTableauRows_dualTableauInsert
        (dualInsertionRows word) x ih

/-- A dominated lower row cannot be longer than its upper row. -/
theorem DualRowDominates.length_le
    {α : Type*} [LE α] {upper lower : List α}
    (hdom : DualRowDominates upper lower) :
    lower.length ≤ upper.length := by
  induction upper generalizing lower with
  | nil =>
      cases lower with
      | nil => simp
      | cons lower lowers => simp [DualRowDominates] at hdom
  | cons upper uppers ih =>
      cases lower with
      | nil => simp
      | cons lower lowers =>
          simp only [DualRowDominates] at hdom
          simpa using Nat.succ_le_succ (ih hdom.2)

end Multisegment

end


/- SOURCE Multisegment/Greene/Tableau.lean -/
section
/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AI-generated by Elazar Gershuni
-/

/-!
# Greene maxima of dual insertion tableaux

This file proves the tableau-counting half of the classical dual Greene
theorem.  Tableau cells are ordered by bottom-to-top row reading.  Strict
rows bound each decreasing support to one cell per row and weak columns give
the matching family of supports.
-/

namespace Multisegment

/-- Weak column dominance is transitive. -/
theorem DualRowDominates.trans
    {α : Type*} [Preorder α] {upper middle lower : List α}
    (hum : DualRowDominates upper middle)
    (hml : DualRowDominates middle lower) :
    DualRowDominates upper lower := by
  induction upper generalizing middle lower with
  | nil =>
      cases middle <;> cases lower <;>
        simp [DualRowDominates] at hum hml ⊢
  | cons u upper ih =>
      cases middle with
      | nil =>
          cases lower <;> simp [DualRowDominates] at hml ⊢
      | cons m middle =>
          cases lower with
          | nil => simp [DualRowDominates]
          | cons l lower =>
              simp only [DualRowDominates] at hum hml ⊢
              exact ⟨hum.1.trans hml.1, ih hum.2 hml.2⟩

/-- Column dominance compares every represented pair of entries. -/
theorem DualRowDominates.get_le
    {α : Type*} [Preorder α] {upper lower : List α}
    (hdom : DualRowDominates upper lower)
    (j : Fin lower.length) :
    upper.get ⟨j.val, j.isLt.trans_le hdom.length_le⟩ ≤
      lower.get j := by
  induction upper generalizing lower with
  | nil =>
      cases lower with
      | nil => exact j.elim0
      | cons l lower => simp [DualRowDominates] at hdom
  | cons u upper ih =>
      cases lower with
      | nil => exact j.elim0
      | cons l lower =>
          simp only [DualRowDominates] at hdom
          cases j using Fin.cases with
          | zero => simpa [List.get_eq_getElem] using hdom.1
          | succ j =>
              simpa [List.get_eq_getElem] using ih hdom.2 j

/-- `getElem` form of pointwise column dominance. -/
theorem DualRowDominates.getElem_le
    {α : Type*} [Preorder α] {upper lower : List α}
    (hdom : DualRowDominates upper lower) {j : ℕ}
    (hj : j < lower.length) :
    upper[j]'(hj.trans_le hdom.length_le) ≤ lower[j]'hj := by
  simpa [List.get_eq_getElem] using hdom.get_le ⟨j, hj⟩

/-- The tail of a raw dual tableau is again a raw dual tableau. -/
theorem IsDualTableauRows.tail
    {α : Type*} [LT α] [LE α] {row : List α} {rows : List (List α)}
    (hrows : IsDualTableauRows (row :: rows)) :
    IsDualTableauRows rows := by
  cases rows with
  | nil => simp [IsDualTableauRows]
  | cons next rows =>
      simpa [IsDualTableauRows] using hrows.2.2

/-- The first row of a nontrivial raw dual tableau dominates the second. -/
theorem IsDualTableauRows.head_dominates
    {α : Type*} [LT α] [LE α]
    {row next : List α} {rows : List (List α)}
    (hrows : IsDualTableauRows (row :: next :: rows)) :
    DualRowDominates row next := by
  simpa [IsDualTableauRows] using hrows.2.1

/-- The first row dominates every later row. -/
theorem IsDualTableauRows.head_dominates_get
    {α : Type*} [Preorder α] {row : List α} {rows : List (List α)}
    (hrows : IsDualTableauRows (row :: rows))
    (j : Fin rows.length) :
    DualRowDominates row (rows.get j) := by
  induction rows generalizing row with
  | nil => exact j.elim0
  | cons next rows ih =>
      cases j using Fin.cases with
      | zero => exact hrows.head_dominates
      | succ j =>
          exact hrows.head_dominates.trans
            (ih hrows.tail j)

/-- Any earlier row of a raw dual tableau dominates any later row. -/
theorem IsDualTableauRows.get_dominates_of_lt
    {α : Type*} [Preorder α] {rows : List (List α)}
    (hrows : IsDualTableauRows rows)
    {i j : Fin rows.length} (hij : i < j) :
    DualRowDominates (rows.get i) (rows.get j) := by
  induction rows with
  | nil => exact i.elim0
  | cons row rows ih =>
      cases i using Fin.cases with
      | zero =>
          cases j using Fin.cases with
          | zero => simp at hij
          | succ j => exact hrows.head_dominates_get j
      | succ i =>
          cases j using Fin.cases with
          | zero => simp at hij
          | succ j =>
              exact ih hrows.tail (Fin.succ_lt_succ_iff.mp hij)

/-- Every represented row of a raw dual tableau is strictly increasing. -/
theorem IsDualTableauRows.get_pairwise
    {α : Type*} [LT α] [LE α] {rows : List (List α)}
    (hrows : IsDualTableauRows rows) (i : Fin rows.length) :
    (rows.get i).Pairwise (fun a b => a < b) := by
  induction rows with
  | nil => exact i.elim0
  | cons row rows ih =>
      cases i using Fin.cases with
      | zero => exact hrows.1
      | succ i => exact ih hrows.tail i

/-- Raw dual tableau row lengths are weakly decreasing. -/
theorem IsDualTableauRows.map_length_sortedGE
    {α : Type*} [Preorder α] {rows : List (List α)}
    (hrows : IsDualTableauRows rows) :
    (rows.map List.length).SortedGE := by
  rw [List.sortedGE_iff_antitone_get]
  intro i j hij
  simp only [List.get_eq_getElem, List.getElem_map]
  rcases hij.eq_or_lt with hij | hij
  · subst j
    rfl
  · exact (hrows.get_dominates_of_lt hij).length_le

/-- Young diagram carried by the row lengths of a raw dual tableau. -/
noncomputable def dualTableauShape
    {α : Type*} [Preorder α] (rows : List (List α))
    (hrows : IsDualTableauRows rows) : YoungDiagram :=
  YoungDiagram.ofRowLens (rows.map List.length)
    hrows.map_length_sortedGE

/-- Shape of the dual insertion tableau of a finite word. -/
noncomputable def dualInsertionShape
    {α : Type*} [LinearOrder α] (word : List α) : YoungDiagram :=
  dualTableauShape (dualInsertionRows word)
    (isDualTableauRows_dualInsertionRows word)

/-- A cell in a list of tableau rows. -/
abbrev DualTableauCell {α : Type*} (rows : List (List α)) :=
  Σ i : Fin rows.length, Fin (rows.get i).length

/-- Numeric position of a cell in top-to-bottom row concatenation. -/
noncomputable def dualTableauCellOffset {α : Type*} {rows : List (List α)}
    (cell : DualTableauCell rows) : ℕ :=
  ((rows.map List.length).take cell.1.val).sum + cell.2.val

/-- Cells in a later row have strictly larger top-to-bottom offsets. -/
theorem dualTableauCellOffset_lt_of_row_lt
    {α : Type*} {rows : List (List α)}
    {x y : DualTableauCell rows} (hxy : x.1 < y.1) :
    dualTableauCellOffset x < dualTableauCellOffset y := by
  have hxBound : x.1.val < (rows.map List.length).length := by
    rw [List.length_map]
    exact x.1.isLt
  have hxStep := List.sum_take_succ
    (rows.map List.length) x.1.val hxBound
  have hxCell : x.2.val < (rows.map List.length)[x.1.val] := by
    rw [List.getElem_map]
    exact x.2.isLt
  have hxlt : dualTableauCellOffset x <
      ((rows.map List.length).take (x.1.val + 1)).sum := by
    rw [hxStep]
    exact Nat.add_lt_add_left hxCell _
  have hmono :
      ((rows.map List.length).take (x.1.val + 1)).sum ≤
        ((rows.map List.length).take y.1.val).sum :=
    List.monotone_sum_take (rows.map List.length) (by omega)
  have hyle : ((rows.map List.length).take y.1.val).sum ≤
      dualTableauCellOffset y := by
    simp [dualTableauCellOffset]
  exact hxlt.trans_le (hmono.trans hyle)

/-- Every cell offset lies inside the flattened row list. -/
theorem dualTableauCellOffset_lt_length_flatten
    {α : Type*} {rows : List (List α)}
    (cell : DualTableauCell rows) :
    dualTableauCellOffset cell < rows.flatten.length := by
  have hiBound : cell.1.val < (rows.map List.length).length := by
    rw [List.length_map]
    exact cell.1.isLt
  have hstep := List.sum_take_succ
    (rows.map List.length) cell.1.val hiBound
  have hcell : cell.2.val <
      (rows.map List.length)[cell.1.val] := by
    rw [List.getElem_map]
    exact cell.2.isLt
  have hlt : dualTableauCellOffset cell <
      ((rows.map List.length).take (cell.1.val + 1)).sum := by
    rw [hstep]
    exact Nat.add_lt_add_left hcell _
  have hmono := List.monotone_sum_take (rows.map List.length)
    (show cell.1.val + 1 ≤ (rows.map List.length).length by omega)
  change ((rows.map List.length).take (cell.1.val + 1)).sum ≤
    ((rows.map List.length).take (rows.map List.length).length).sum at hmono
  rw [List.take_length, ← List.length_flatten] at hmono
  exact hlt.trans_le hmono

/-- A tableau cell as its certified flattened-list position. -/
noncomputable def dualTableauCellFin {α : Type*} {rows : List (List α)}
    (cell : DualTableauCell rows) : Fin rows.flatten.length :=
  ⟨dualTableauCellOffset cell,
    dualTableauCellOffset_lt_length_flatten cell⟩

/-- The tableau cell type has one element per entry of the flattened rows. -/
theorem card_dualTableauCell
    {α : Type*} (rows : List (List α)) :
    Fintype.card (DualTableauCell rows) = rows.flatten.length := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [← List.sum_ofFn]
  have hlist :
      List.ofFn (fun i : Fin rows.length => (rows.get i).length) =
        rows.map List.length := by
    calc
      List.ofFn (fun i : Fin rows.length => (rows.get i).length) =
          (List.ofFn rows.get).map List.length := by
        rw [List.map_ofFn]
        rfl
      _ = rows.map List.length := by rw [List.ofFn_get]
  rw [hlist, ← List.length_flatten]

/-- Distinct tableau cells have distinct concatenation offsets. -/
theorem dualTableauCellOffset_injective
    {α : Type*} {rows : List (List α)} :
    Function.Injective
      (dualTableauCellOffset (α := α) (rows := rows)) := by
  rintro ⟨i, j⟩ ⟨k, l⟩ h
  have hik : i = k := by
    apply le_antisymm
    · by_contra hnot
      have hki : k < i := lt_of_not_ge hnot
      exact (dualTableauCellOffset_lt_of_row_lt
        (x := ⟨k, l⟩) (y := ⟨i, j⟩) hki).ne h.symm
    · by_contra hnot
      have hik : i < k := lt_of_not_ge hnot
      exact (dualTableauCellOffset_lt_of_row_lt
        (x := ⟨i, j⟩) (y := ⟨k, l⟩) hik).ne h
  subst k
  have hjl : j = l := by
    apply Fin.ext
    change ((rows.map List.length).take i.val).sum + j.val =
      ((rows.map List.length).take i.val).sum + l.val at h
    omega
  subst l
  rfl

/-- The certified flattened-position map is injective. -/
theorem dualTableauCellFin_injective
    {α : Type*} {rows : List (List α)} :
    Function.Injective (dualTableauCellFin (α := α) (rows := rows)) := by
  intro x y hxy
  apply dualTableauCellOffset_injective
  exact congrArg Fin.val hxy

/-- Every flattened-list position comes from a unique tableau cell. -/
theorem dualTableauCellFin_bijective
    {α : Type*} {rows : List (List α)} :
    Function.Bijective (dualTableauCellFin (α := α) (rows := rows)) := by
  exact (Fintype.bijective_iff_injective_and_card
    (dualTableauCellFin (α := α) (rows := rows))).2
      ⟨dualTableauCellFin_injective,
        (card_dualTableauCell rows).trans (Fintype.card_fin _).symm⟩

noncomputable instance instLinearOrderDualTableauCell
    {α : Type*} (rows : List (List α)) :
    LinearOrder (DualTableauCell rows) :=
  LinearOrder.lift' dualTableauCellOffset
    dualTableauCellOffset_injective

noncomputable instance (priority := 2000) instLEDualTableauCell
    {α : Type*} (rows : List (List α)) : LE (DualTableauCell rows) :=
  (instLinearOrderDualTableauCell rows).toLE

noncomputable instance (priority := 2000) instLTDualTableauCell
    {α : Type*} (rows : List (List α)) : LT (DualTableauCell rows) :=
  (instLinearOrderDualTableauCell rows).toLT

/-- Row-reading order identifies tableau cells with their flattened `Fin`
positions. -/
noncomputable def dualTableauCellOrderIsoFin
    {α : Type*} (rows : List (List α)) :
    DualTableauCell rows ≃o Fin rows.flatten.length :=
  RelIso.mk
    (Equiv.ofBijective dualTableauCellFin
      dualTableauCellFin_bijective)
    (by intro x y; rfl)

/-- Entry carried by a raw tableau cell. -/
noncomputable def dualTableauCellEntry {α : Type*} {rows : List (List α)}
    (cell : DualTableauCell rows) : α :=
  (rows.get cell.1).get cell.2

/-- Looking up a cell's flattened position recovers its tableau entry. -/
theorem get_dualTableauCellFin
    {α : Type*} (rows : List (List α))
    (cell : DualTableauCell rows) :
    rows.flatten.get (dualTableauCellFin cell) =
      dualTableauCellEntry cell := by
  induction rows with
  | nil => exact cell.1.elim0
  | cons row rows ih =>
      rcases cell with ⟨i, j⟩
      cases i using Fin.cases with
      | zero =>
          rcases j with ⟨j, hj⟩
          change j < row.length at hj
          convert (List.getElem_append_left (as := row) (bs := rows.flatten) hj) using 1 <;>
            simp [dualTableauCellFin, dualTableauCellOffset,
              dualTableauCellEntry, List.get_eq_getElem] <;> first | rfl | omega
      | succ i =>
          have htail := ih ⟨i, j⟩
          simp [dualTableauCellFin, dualTableauCellOffset,
            dualTableauCellEntry, List.get_eq_getElem, Nat.add_comm] at htail ⊢
          rw [List.getElem_append_right (by omega)]
          have hindex :
              (↑j + (row.length +
                  (List.take (↑i) (List.map List.length rows)).sum) -
                row.length) =
                ↑j + (List.take (↑i) (List.map List.length rows)).sum := by
            omega
          simpa only [hindex] using htail

/-- In bottom-to-top row reading, entries in a fixed column weakly decrease. -/
theorem dualTableauCellEntry_reverse_le_of_same_column
    {α : Type*} [LinearOrder α] {rows : List (List α)}
    (hrows : IsDualTableauRows rows)
    {x y : DualTableauCell rows.reverse} (hxy : x < y)
    (hcolumn : x.2.val = y.2.val) :
    dualTableauCellEntry y ≤ dualTableauCellEntry x := by
  have hxyOffset : dualTableauCellOffset x <
      dualTableauCellOffset y := hxy
  have hrow_ne : x.1 ≠ y.1 := by
    intro hrow
    have hoff : dualTableauCellOffset x =
        dualTableauCellOffset y := by
      simp [dualTableauCellOffset, hrow, hcolumn]
    exact hxyOffset.ne hoff
  have hrow : x.1 < y.1 := by
    rcases lt_trichotomy x.1 y.1 with h | h | h
    · exact h
    · exact (hrow_ne h).elim
    · exact (dualTableauCellOffset_lt_of_row_lt h).asymm
        hxyOffset |>.elim
  have hxlt : x.1.val < rows.length := by simpa using x.1.isLt
  have hylt : y.1.val < rows.length := by simpa using y.1.isLt
  let ix : Fin rows.length :=
    ⟨rows.length - 1 - x.1.val, by omega⟩
  let iy : Fin rows.length :=
    ⟨rows.length - 1 - y.1.val, by omega⟩
  have hiyx : iy < ix := by
    change rows.length - 1 - y.1.val <
      rows.length - 1 - x.1.val
    omega
  have hxrow : rows.reverse.get x.1 = rows.get ix := by
    simpa only [List.get_eq_getElem, ix] using
      (List.getElem_reverse (l := rows) (i := x.1.val) x.1.isLt)
  have hyrow : rows.reverse.get y.1 = rows.get iy := by
    simpa only [List.get_eq_getElem, iy] using
      (List.getElem_reverse (l := rows) (i := y.1.val) y.1.isLt)
  have hxcol : x.2.val < (rows.get ix).length := by
    rw [← hxrow]
    exact x.2.isLt
  have hle := (hrows.get_dominates_of_lt hiyx).getElem_le hxcol
  simpa [dualTableauCellEntry, List.get_eq_getElem,
    hxrow, hyrow, hcolumn] using hle

/-- Reversing the row list preserves strictness of every represented row. -/
theorem IsDualTableauRows.reverse_get_pairwise
    {α : Type*} [LinearOrder α] {rows : List (List α)}
    (hrows : IsDualTableauRows rows)
    (i : Fin rows.reverse.length) :
    (rows.reverse.get i).Pairwise (fun a b => a < b) := by
  have hilt : i.val < rows.length := by simpa using i.isLt
  let original : Fin rows.length :=
    ⟨rows.length - 1 - i.val, by omega⟩
  have hirow : rows.reverse.get i = rows.get original := by
    simpa only [List.get_eq_getElem, original] using
      (List.getElem_reverse (l := rows) (i := i.val) i.isLt)
  rw [hirow]
  exact hrows.get_pairwise original

/-! ## Greene colorings on arbitrary finite linear orders -/

/-- A color class is weakly decreasing along an arbitrary finite linear
order of positions. -/
noncomputable def IsOrderedWordColoringSupport
    {ι α : Type*} [Fintype ι] [LinearOrder ι] [LE α]
    {J : ℕ} (word : ι → α) (coloring : ι → Option (Fin J)) : Prop :=
  ∀ k,
    ∀ i ∈ (Finset.univ.filter fun i => coloring i = some k),
      ∀ j ∈ (Finset.univ.filter fun j => coloring j = some k),
        i < j → word j ≤ word i

/-- Colored positions in an arbitrary finite ordered word. -/
noncomputable def orderedWordColoringCover
    {ι : Type*} [Fintype ι] {J : ℕ}
    (coloring : ι → Option (Fin J)) : Finset ι :=
  Finset.univ.filter fun i => (coloring i).isSome

/-- Color the first `J` columns by their column indices. -/
noncomputable def dualTableauColumnColoring
    {α : Type*} {rows : List (List α)} (J : ℕ) :
    DualTableauCell rows → Option (Fin J) :=
  fun cell =>
    if h : cell.2.val < J then some ⟨cell.2.val, h⟩ else none

/-- For a raw dual tableau, columns of the bottom-to-top reading are weakly
decreasing color classes. -/
theorem isOrderedWordColoringSupport_dualTableauColumnColoring
    {α : Type*} [LinearOrder α] {rows : List (List α)}
    (hrows : IsDualTableauRows rows) (J : ℕ) :
    IsOrderedWordColoringSupport
      (dualTableauCellEntry (α := α) (rows := rows.reverse))
      (dualTableauColumnColoring (rows := rows.reverse) J) := by
  intro k i hi j hj hij
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  have hiColumn : i.2.val = k.val := by
    by_cases hlt : i.2.val < J
    · simp [dualTableauColumnColoring, hlt] at hi
      exact congrArg Fin.val hi
    · simp [dualTableauColumnColoring, hlt] at hi
  have hjColumn : j.2.val = k.val := by
    by_cases hlt : j.2.val < J
    · simp [dualTableauColumnColoring, hlt] at hj
      exact congrArg Fin.val hj
    · simp [dualTableauColumnColoring, hlt] at hj
  exact dualTableauCellEntry_reverse_le_of_same_column hrows hij
    (hiColumn.trans hjColumn.symm)

/-- The colored cells lying in one fixed row. -/
noncomputable def orderedWordColoringRowFiber
    {α : Type*} {rows : List (List α)} {J : ℕ}
    (coloring : DualTableauCell rows → Option (Fin J))
    (i : Fin rows.length) : Finset (DualTableauCell rows) :=
  (orderedWordColoringCover coloring).filter fun cell => cell.1 = i

/-- In a strictly increasing row, an admissible weakly decreasing coloring
uses each color at most once.  The row fiber is consequently bounded by both
the color count and the row length. -/
theorem card_orderedWordColoringRowFiber_le_min
    {α : Type*} [LinearOrder α] {rows : List (List α)} {J : ℕ}
    {coloring : DualTableauCell rows → Option (Fin J)}
    (hcoloring : IsOrderedWordColoringSupport
      (dualTableauCellEntry (α := α) (rows := rows)) coloring)
    (hstrict : ∀ i, (rows.get i).Pairwise (fun a b => a < b))
    (i : Fin rows.length) :
    (orderedWordColoringRowFiber coloring i).card ≤
      Nat.min J (rows.get i).length := by
  rw [Nat.le_min]
  constructor
  · calc
      (orderedWordColoringRowFiber coloring i).card ≤
          ((Finset.univ : Finset (Option (Fin J))).erase none).card := by
        apply Finset.card_le_card_of_injOn coloring
        · intro cell hcell
          have hcover := (Finset.mem_filter.mp hcell).1
          have hsome := (Finset.mem_filter.mp hcover).2
          simpa using Option.isSome_iff_ne_none.mp hsome
        · intro x hx y hy hxyColor
          have hxData := Finset.mem_filter.mp hx
          have hyData := Finset.mem_filter.mp hy
          have hxRow : x.1 = i := hxData.2
          have hyRow : y.1 = i := hyData.2
          have hxSome := (Finset.mem_filter.mp hxData.1).2
          cases hxColor : coloring x with
          | none => simp [hxColor] at hxSome
          | some k =>
              have hyColor : coloring y = some k :=
                hxyColor.symm.trans hxColor
              have sameColorContradiction
                  {p q : DualTableauCell rows}
                  (hpRow : p.1 = i) (hqRow : q.1 = i)
                  (hpColor : coloring p = some k)
                  (hqColor : coloring q = some k)
                  (hpq : p.2.val < q.2.val) : False := by
                have hpqCell : p < q := by
                  change dualTableauCellOffset p < dualTableauCellOffset q
                  simp [dualTableauCellOffset, hpRow, hqRow]
                  exact hpq
                let pc : Fin (rows.get i).length :=
                  ⟨p.2.val, by simpa [hpRow] using p.2.isLt⟩
                let qc : Fin (rows.get i).length :=
                  ⟨q.2.val, by simpa [hqRow] using q.2.isLt⟩
                have hpqColumn : pc < qc := by
                  exact hpq
                have hentry := (hstrict i).rel_get_of_lt hpqColumn
                have hdecreasing := hcoloring k p
                  (by simp [hpColor]) q (by simp [hqColor]) hpqCell
                have hentry' : dualTableauCellEntry p <
                    dualTableauCellEntry q := by
                  simpa [dualTableauCellEntry, List.get_eq_getElem,
                    pc, qc, hpRow, hqRow] using hentry
                exact (not_le_of_gt hentry') hdecreasing
              rcases lt_trichotomy x.2.val y.2.val with hlt | heq | hgt
              · exact (sameColorContradiction hxRow hyRow
                  hxColor hyColor hlt).elim
              · apply dualTableauCellOffset_injective
                simp [dualTableauCellOffset, hxRow, hyRow, heq]
              · exact (sameColorContradiction hyRow hxRow
                  hyColor hxColor hgt).elim
      _ = J := by simp
  · calc
      (orderedWordColoringRowFiber coloring i).card ≤
          (Finset.range (rows.get i).length).card := by
        apply Finset.card_le_card_of_injOn (fun cell => cell.2.val)
        · intro cell hcell
          have hrow := (Finset.mem_filter.mp hcell).2
          simpa [hrow] using cell.2.isLt
        · intro x hx y hy hxy
          have hxRow := (Finset.mem_filter.mp hx).2
          have hyRow := (Finset.mem_filter.mp hy).2
          apply dualTableauCellOffset_injective
          simp [dualTableauCellOffset, hxRow, hyRow, hxy]
      _ = (rows.get i).length := Finset.card_range _

/-- Coverage cardinality decomposes as the sum of its row fibers. -/
theorem card_orderedWordColoringCover_eq_sum_rowFiber
    {α : Type*} {rows : List (List α)} {J : ℕ}
    (coloring : DualTableauCell rows → Option (Fin J)) :
    (orderedWordColoringCover coloring).card =
      ∑ i : Fin rows.length,
        (orderedWordColoringRowFiber coloring i).card := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun cell : DualTableauCell rows => cell.1)
    (s := orderedWordColoringCover coloring)
    (t := Finset.univ) (by simp)
  simpa [orderedWordColoringRowFiber] using h

/-- Number of cells in the first `J` columns of a list of rows. -/
noncomputable def dualTableauRowPrefixCount {α : Type*}
    (rows : List (List α)) (J : ℕ) : ℕ :=
  ∑ i : Fin rows.length, Nat.min J (rows.get i).length

/-- List-sum form of the row prefix count. -/
theorem dualTableauRowPrefixCount_eq_sum_map
    {α : Type*} (rows : List (List α)) (J : ℕ) :
    dualTableauRowPrefixCount rows J =
      (rows.map fun row => Nat.min J row.length).sum := by
  unfold dualTableauRowPrefixCount
  rw [← List.sum_ofFn]
  congr 1
  calc
    List.ofFn (fun i : Fin rows.length =>
        Nat.min J (rows.get i).length) =
        (List.ofFn rows.get).map fun row => Nat.min J row.length := by
      rw [List.map_ofFn]
      rfl
    _ = (rows.map fun row => Nat.min J row.length) := by
      rw [List.ofFn_get]

/-- Reversing the row list does not change the number of cells in its first
`J` columns. -/
@[simp]
theorem dualTableauRowPrefixCount_reverse
    {α : Type*} (rows : List (List α)) (J : ℕ) :
    dualTableauRowPrefixCount rows.reverse J =
      dualTableauRowPrefixCount rows J := by
  rw [dualTableauRowPrefixCount_eq_sum_map,
    dualTableauRowPrefixCount_eq_sum_map]
  simp

/-- A column of a diagram built from row lengths consists exactly of the row
indices whose lengths exceed that column. -/
theorem YoungDiagram.colLen_ofRowLens_eq_card_filter
    (w : List ℕ) (hw : w.SortedGE) (k : ℕ) :
    (YoungDiagram.ofRowLens w hw).colLen k =
      ((Finset.univ : Finset (Fin w.length)).filter
        fun i => k < w.get i).card := by
  rw [YoungDiagram.colLen_eq_card]
  apply Finset.card_bij
    (fun p hp =>
      ⟨p.1, (YoungDiagram.mem_ofRowLens.mp
        (YoungDiagram.mem_col_iff.mp hp).1).choose⟩)
  · intro p hp
    have hpCol := YoungDiagram.mem_col_iff.mp hp
    have hpShape := YoungDiagram.mem_ofRowLens.mp hpCol.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change k < w[p.1]'hpShape.choose
    rw [← hpCol.2]
    exact hpShape.choose_spec
  · intro p hp q hq hpq
    apply Prod.ext
    · exact congrArg Fin.val hpq
    · exact (YoungDiagram.mem_col_iff.mp hp).2.trans
        (YoungDiagram.mem_col_iff.mp hq).2.symm
  · intro i hi
    have hik := (Finset.mem_filter.mp hi).2
    refine ⟨(i.val, k), ?_, ?_⟩
    · rw [YoungDiagram.mk_mem_col_iff,
        YoungDiagram.mem_ofRowLens]
      exact ⟨i.isLt, by simpa [List.get_eq_getElem] using hik⟩
    · apply Fin.ext
      rfl

/-- Counting indices below both `J` and `n`. -/
theorem sum_range_ite_lt (J n : ℕ) :
    (∑ k ∈ Finset.range J, if k < n then 1 else 0) =
      Nat.min J n := by
  calc
    (∑ k ∈ Finset.range J, if k < n then 1 else 0) =
        ((Finset.range J).filter fun k => k < n).card := by
      exact Finset.sum_boole (fun k => k < n) (Finset.range J)
    _ = (Finset.range (Nat.min J n)).card := by
      congr 1
      ext k
      simp
    _ = Nat.min J n := Finset.card_range _

/-- Cumulative column lengths of a diagram built from row lengths count the
same first-`J` cells as summing the truncated row lengths. -/
theorem YoungDiagram.sum_colLen_ofRowLens_eq_sum_min
    (w : List ℕ) (hw : w.SortedGE) (J : ℕ) :
    (∑ k ∈ Finset.range J,
      (YoungDiagram.ofRowLens w hw).colLen k) =
      ∑ i : Fin w.length, Nat.min J (w.get i) := by
  simp_rw [YoungDiagram.colLen_ofRowLens_eq_card_filter]
  calc
    (∑ k ∈ Finset.range J,
        ((Finset.univ : Finset (Fin w.length)).filter
          fun i => k < w.get i).card) =
        ∑ k ∈ Finset.range J,
          ∑ i : Fin w.length, if k < w.get i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      exact (Finset.sum_boole
        (fun i : Fin w.length => k < w.get i) Finset.univ).symm
    _ = ∑ i : Fin w.length,
        ∑ k ∈ Finset.range J,
          if k < w.get i then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin w.length, Nat.min J (w.get i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact sum_range_ite_lt J (w.get i)

/-- The `YoungDiagram` attached to raw dual tableau rows has the expected
cumulative column count. -/
theorem sum_colLen_dualTableauShape
    {α : Type*} [Preorder α] (rows : List (List α))
    (hrows : IsDualTableauRows rows) (J : ℕ) :
    (∑ k ∈ Finset.range J,
      (dualTableauShape rows hrows).colLen k) =
      dualTableauRowPrefixCount rows J := by
  rw [dualTableauRowPrefixCount_eq_sum_map]
  calc
    (∑ k ∈ Finset.range J,
        (dualTableauShape rows hrows).colLen k) =
        ∑ i : Fin (rows.map List.length).length,
          Nat.min J ((rows.map List.length).get i) := by
      exact YoungDiagram.sum_colLen_ofRowLens_eq_sum_min
        (rows.map List.length) hrows.map_length_sortedGE J
    _ = (rows.map fun row => Nat.min J row.length).sum := by
      rw [← List.sum_ofFn]
      congr 1
      calc
        List.ofFn (fun i : Fin (rows.map List.length).length =>
            Nat.min J ((rows.map List.length).get i)) =
            (rows.map List.length).map (Nat.min J) := by
          apply List.ext_get (by simp)
          intro i hi hj
          simp [List.get_eq_getElem]
        _ = rows.map (fun row => Nat.min J row.length) := by
          rw [List.map_map]
          rfl

/-- Among `Fin n`, exactly `min J n` indices lie below `J`. -/
theorem card_filter_fin_val_lt (n J : ℕ) :
    ((Finset.univ : Finset (Fin n)).filter fun i => i.val < J).card =
      Nat.min J n := by
  have hcard :
      ((Finset.univ : Finset (Fin n)).filter fun i => i.val < J).card =
        (Finset.univ : Finset (Fin (Nat.min J n))).card := by
    apply Finset.card_bij
      (fun i hi => ⟨i.val, Nat.lt_min.mpr
        ⟨(Finset.mem_filter.mp hi).2, i.isLt⟩⟩)
    · intro i hi
      exact Finset.mem_univ _
    · intro i hi j hj hij
      exact Fin.ext (congrArg
        (fun z : Fin (Nat.min J n) => z.val) hij)
    · intro k _
      let i : Fin n :=
        ⟨k.val, k.isLt.trans_le (Nat.min_le_right J n)⟩
      refine ⟨i, ?_, ?_⟩
      · simp [i, (Nat.lt_min.mp k.isLt).1]
      · apply Fin.ext
        rfl
  simpa using hcard

/-- In each row, the explicit column coloring covers precisely the cells in
the first `J` columns. -/
theorem card_dualTableauColumnColoring_rowFiber
    {α : Type*} {rows : List (List α)} (J : ℕ)
    (i : Fin rows.length) :
    (orderedWordColoringRowFiber
      (dualTableauColumnColoring (rows := rows) J) i).card =
        Nat.min J (rows.get i).length := by
  have hcard :
      (orderedWordColoringRowFiber
        (dualTableauColumnColoring (rows := rows) J) i).card =
      ((Finset.univ : Finset (Fin (rows.get i).length)).filter
        fun j => j.val < J).card := by
    apply Finset.card_bij
      (fun cell hcell =>
        ⟨cell.2.val, by
          have hrow := (Finset.mem_filter.mp hcell).2
          simpa [hrow] using cell.2.isLt⟩)
    · intro cell hcell
      have hcover := (Finset.mem_filter.mp hcell).1
      have hsome := (Finset.mem_filter.mp hcover).2
      have hlt : cell.2.val < J := by
        by_cases h : cell.2.val < J
        · exact h
        · simp [dualTableauColumnColoring, h] at hsome
      simp [hlt]
    · intro x hx y hy hxy
      have hxRow := (Finset.mem_filter.mp hx).2
      have hyRow := (Finset.mem_filter.mp hy).2
      apply dualTableauCellOffset_injective
      have hcolumn : x.2.val = y.2.val := by
        simpa using congrArg
          (fun z : Fin (rows.get i).length => z.val) hxy
      simp [dualTableauCellOffset, hxRow, hyRow, hcolumn]
    · intro j hj
      have hjlt := (Finset.mem_filter.mp hj).2
      refine ⟨⟨i, j⟩, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        constructor
        · simp [orderedWordColoringCover,
            dualTableauColumnColoring, hjlt]
        · rfl
      · apply Fin.ext
        rfl
  exact hcard.trans (card_filter_fin_val_lt _ _)

/-- The explicit column coloring covers exactly the first `J` columns. -/
theorem card_orderedWordColoringCover_dualTableauColumnColoring
    {α : Type*} (rows : List (List α)) (J : ℕ) :
    (orderedWordColoringCover
      (dualTableauColumnColoring (rows := rows) J)).card =
        dualTableauRowPrefixCount rows J := by
  calc
    (orderedWordColoringCover
        (dualTableauColumnColoring (rows := rows) J)).card =
        ∑ i : Fin rows.length,
          (orderedWordColoringRowFiber
            (dualTableauColumnColoring (rows := rows) J) i).card :=
      card_orderedWordColoringCover_eq_sum_rowFiber _
    _ = dualTableauRowPrefixCount rows J := by
      unfold dualTableauRowPrefixCount
      apply Finset.sum_congr rfl
      intro i _
      exact card_dualTableauColumnColoring_rowFiber J i

instance instDecidablePredIsOrderedWordColoringSupport
    {ι α : Type*} [Fintype ι] [LinearOrder ι] [LinearOrder α]
    {J : ℕ} (word : ι → α) :
    DecidablePred (IsOrderedWordColoringSupport (J := J) word) :=
  fun coloring => inferInstanceAs
    (Decidable (∀ k,
      ∀ i ∈ (Finset.univ.filter fun i => coloring i = some k),
        ∀ j ∈ (Finset.univ.filter fun j => coloring j = some k),
          i < j → word j ≤ word i))

/-- Maximum coverage by `J` weakly decreasing color classes on an arbitrary
finite linear order of positions. -/
noncomputable def orderedWordColoringGreeneMax
    {ι α : Type*} [Fintype ι] [LinearOrder ι] [LinearOrder α]
    (word : ι → α) (J : ℕ) : ℕ :=
  ((Finset.univ : Finset (ι → Option (Fin J))).filter
      (IsOrderedWordColoringSupport word)).sup fun coloring =>
    (orderedWordColoringCover coloring).card

/-- Strict rows give the row-by-row upper bound for the ordered Greene
maximum. -/
theorem orderedWordColoringGreeneMax_le_dualTableauRowPrefixCount
    {α : Type*} [LinearOrder α] {rows : List (List α)}
    (hstrict : ∀ i, (rows.get i).Pairwise (fun a b => a < b))
    (J : ℕ) :
    orderedWordColoringGreeneMax
        (dualTableauCellEntry (α := α) (rows := rows)) J ≤
      dualTableauRowPrefixCount rows J := by
  unfold orderedWordColoringGreeneMax
  apply Finset.sup_le
  intro coloring hcoloring
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcoloring
  calc
    (orderedWordColoringCover coloring).card =
        ∑ i : Fin rows.length,
          (orderedWordColoringRowFiber coloring i).card :=
      card_orderedWordColoringCover_eq_sum_rowFiber coloring
    _ ≤ dualTableauRowPrefixCount rows J := by
      unfold dualTableauRowPrefixCount
      apply Finset.sum_le_sum
      intro i _
      exact card_orderedWordColoringRowFiber_le_min
        hcoloring hstrict i

/-- The column coloring attains the first-`J`-columns count for the
bottom-to-top reading of a raw dual tableau. -/
theorem dualTableauRowPrefixCount_le_orderedWordColoringGreeneMax_reverse
    {α : Type*} [LinearOrder α] {rows : List (List α)}
    (hrows : IsDualTableauRows rows) (J : ℕ) :
    dualTableauRowPrefixCount rows.reverse J ≤
      orderedWordColoringGreeneMax
        (dualTableauCellEntry (α := α) (rows := rows.reverse)) J := by
  letI : DecidableEq (DualTableauCell rows.reverse) :=
    LinearOrder.toDecidableEq
  rw [← card_orderedWordColoringCover_dualTableauColumnColoring]
  unfold orderedWordColoringGreeneMax
  have hmem :
      dualTableauColumnColoring (rows := rows.reverse) J ∈
        (Finset.univ.filter fun coloring =>
          IsOrderedWordColoringSupport
            (dualTableauCellEntry (α := α) (rows := rows.reverse))
            coloring) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      isOrderedWordColoringSupport_dualTableauColumnColoring hrows J⟩
  exact Finset.le_sup
    (f := fun coloring : DualTableauCell rows.reverse → Option (Fin J) =>
      (orderedWordColoringCover coloring).card) hmem

/-- Tableau Greene counting: the weakly decreasing `J`-family maximum of
the bottom-to-top row reading is exactly the number of cells in its first
`J` columns. -/
theorem orderedWordColoringGreeneMax_dualTableauCellEntry_reverse
    {α : Type*} [LinearOrder α] {rows : List (List α)}
    (hrows : IsDualTableauRows rows) (J : ℕ) :
    orderedWordColoringGreeneMax
        (dualTableauCellEntry (α := α) (rows := rows.reverse)) J =
      dualTableauRowPrefixCount rows.reverse J := by
  apply Nat.le_antisymm
  · exact orderedWordColoringGreeneMax_le_dualTableauRowPrefixCount
      hrows.reverse_get_pairwise J
  · exact
      dualTableauRowPrefixCount_le_orderedWordColoringGreeneMax_reverse
        hrows J

/-- On `Fin n`, the generic statistic is the existing coloring-form word
Greene maximum. -/
theorem orderedWordColoringGreeneMax_fin
    {α : Type*} [LinearOrder α] {n : ℕ}
    (word : FiniteWord α n) (J : ℕ) :
    orderedWordColoringGreeneMax word J =
      wordColoringGreeneMax word J := by
  unfold orderedWordColoringGreeneMax wordColoringGreeneMax
  unfold IsOrderedWordColoringSupport IsWordColoringSupport
  unfold IsWeaklyDecreasingSubsequence wordColorBlock
  unfold orderedWordColoringCover wordColoringCover
  congr 1
  ext coloring
  simp

/-- Reindexing a coloring along an equivalence preserves its coverage
cardinality. -/
theorem card_orderedWordColoringCover_comp_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {J : ℕ} (e : ι ≃ κ) (coloring : κ → Option (Fin J)) :
    (orderedWordColoringCover (coloring ∘ e)).card =
      (orderedWordColoringCover coloring).card := by
  apply Finset.card_bij (fun i _ => e i)
  · intro i hi
    simpa [orderedWordColoringCover] using hi
  · intro i _ j _ hij
    exact e.injective hij
  · intro j hj
    refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
    simpa [orderedWordColoringCover] using hj

/-- Pulling both a word and its coloring back along an order isomorphism
preserves admissibility. -/
theorem isOrderedWordColoringSupport_comp_orderIso
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [LinearOrder ι] [LinearOrder κ] [LE α] {J : ℕ}
    (e : ι ≃o κ) {word : κ → α} {coloring : κ → Option (Fin J)}
    (hcoloring : IsOrderedWordColoringSupport word coloring) :
    IsOrderedWordColoringSupport (word ∘ e) (coloring ∘ e) := by
  intro k i hi j hj hij
  apply hcoloring k (e i)
  · simpa using hi
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by simpa using hj⟩
  · exact e.lt_iff_lt.mpr hij

/-- Greene maxima are invariant under an order isomorphism of word
positions. -/
theorem orderedWordColoringGreeneMax_comp_orderIso
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    [LinearOrder ι] [LinearOrder κ] [LinearOrder α]
    (e : ι ≃o κ) (word : κ → α) (J : ℕ) :
    orderedWordColoringGreeneMax (word ∘ e) J =
      orderedWordColoringGreeneMax word J := by
  apply Nat.le_antisymm
  · unfold orderedWordColoringGreeneMax
    apply Finset.sup_le
    intro coloring hcoloring
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcoloring
    let transported : κ → Option (Fin J) := coloring ∘ e.symm
    have htransported :
        IsOrderedWordColoringSupport word transported := by
      have h := isOrderedWordColoringSupport_comp_orderIso
        e.symm hcoloring
      simpa [transported, Function.comp_def] using h
    rw [← card_orderedWordColoringCover_comp_equiv e.symm.toEquiv coloring]
    have hle := Finset.le_sup
      (f := fun coloring : κ → Option (Fin J) =>
        (orderedWordColoringCover coloring).card)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htransported⟩)
    simpa [transported] using hle
  · unfold orderedWordColoringGreeneMax
    apply Finset.sup_le
    intro coloring hcoloring
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcoloring
    let transported : ι → Option (Fin J) := coloring ∘ e
    have htransported :
        IsOrderedWordColoringSupport (word ∘ e) transported :=
      isOrderedWordColoringSupport_comp_orderIso e hcoloring
    rw [← card_orderedWordColoringCover_comp_equiv e.toEquiv coloring]
    have hle := Finset.le_sup
      (f := fun transported : ι → Option (Fin J) =>
        (orderedWordColoringCover transported).card)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htransported⟩)
    simpa [transported] using hle

/-- The ordered-cell Greene maximum is the list-word Greene maximum of the
top-to-bottom row concatenation. -/
theorem orderedWordColoringGreeneMax_dualTableauCellEntry
    {α : Type*} [LinearOrder α] (rows : List (List α)) (J : ℕ) :
    orderedWordColoringGreeneMax
        (dualTableauCellEntry (α := α) (rows := rows)) J =
      listWordGreeneMax rows.flatten J := by
  let e := dualTableauCellOrderIsoFin rows
  have hword :
      dualTableauCellEntry (α := α) (rows := rows) =
        rows.flatten.get ∘ e := by
    funext cell
    exact (get_dualTableauCellFin rows cell).symm
  rw [hword, orderedWordColoringGreeneMax_comp_orderIso]
  rw [orderedWordColoringGreeneMax_fin,
    wordColoringGreeneMax_eq_wordGreeneMax]
  rfl

/-- The bottom-to-top reading word of a raw dual tableau satisfies the dual
Greene formula. -/
theorem listWordGreeneMax_dualTableauWord
    {α : Type*} [LinearOrder α] {rows : List (List α)}
    (hrows : IsDualTableauRows rows) (J : ℕ) :
    listWordGreeneMax (dualTableauWord rows) J =
      dualTableauRowPrefixCount rows.reverse J := by
  calc
    listWordGreeneMax (dualTableauWord rows) J =
        orderedWordColoringGreeneMax
          (dualTableauCellEntry (α := α) (rows := rows.reverse)) J := by
      simpa [dualTableauWord] using
        (orderedWordColoringGreeneMax_dualTableauCellEntry
          (rows := rows.reverse) J).symm
    _ = dualTableauRowPrefixCount rows.reverse J :=
      orderedWordColoringGreeneMax_dualTableauCellEntry_reverse hrows J

/-- Classical dual Greene theorem for the row-strict, column-weak insertion
normal form: the `J`-family maximum of a word is the number of insertion
tableau cells in its first `J` columns. -/
theorem listWordGreeneMax_eq_dualInsertionRowPrefixCount
    {α : Type*} [LinearOrder α] (word : List α) (J : ℕ) :
    listWordGreeneMax word J =
      dualTableauRowPrefixCount (dualInsertionRows word).reverse J := by
  calc
    listWordGreeneMax word J =
        listWordGreeneMax
          (dualTableauWord (dualInsertionRows word)) J :=
      listWordGreeneMax_dualInsertionRows word J
    _ = dualTableauRowPrefixCount
        (dualInsertionRows word).reverse J :=
      listWordGreeneMax_dualTableauWord
        (isDualTableauRows_dualInsertionRows word) J

/-- Shape-valued classical dual Greene theorem: cumulative column lengths of
the dual insertion shape equal the word Greene maxima. -/
theorem sum_colLen_dualInsertionShape_eq_listWordGreeneMax
    {α : Type*} [LinearOrder α] (word : List α) (J : ℕ) :
    (∑ k ∈ Finset.range J,
      (dualInsertionShape word).colLen k) =
      listWordGreeneMax word J := by
  calc
    (∑ k ∈ Finset.range J,
        (dualInsertionShape word).colLen k) =
        dualTableauRowPrefixCount (dualInsertionRows word) J := by
      exact sum_colLen_dualTableauShape
        (dualInsertionRows word)
        (isDualTableauRows_dualInsertionRows word) J
    _ = dualTableauRowPrefixCount
        (dualInsertionRows word).reverse J :=
      (dualTableauRowPrefixCount_reverse
        (dualInsertionRows word) J).symm
    _ = listWordGreeneMax word J :=
      (listWordGreeneMax_eq_dualInsertionRowPrefixCount word J).symm

end Multisegment

end

#print axioms Multisegment.sum_colLen_dualInsertionShape_eq_listWordGreeneMax

#print axioms FourPapers.Symmetric.symbolicGenerators_one_groebner
#print axioms FourPapers.Symmetric.mixedGroebner_of_positiveBounds
#print axioms FourPapers.Symmetric.mixedGroebner_cons_one
#print axioms FourPapers.Symmetric.integralBaseChangeAssertion_of_compatible
#print axioms FourPapers.Symmetric.symbolicPower_map_coeff_of_fraction_groebner
#print axioms FourPapers.Symmetric.symbolicPower_comap_chart
#print axioms MonomialOrder.ideal_eq_of_le_of_initial_le
#print axioms FourPapers.Symmetric.Reduction.positiveCore_implies_compatible
#print axioms FourPapers.Symmetric.Reduction.positiveCore_implies_integral
#print axioms Multisegment.sum_colLen_dualInsertionShape_eq_listWordGreeneMax

/- RECONSTRUCTED SOURCE FinitePolynomialRegular.lean -/
section

set_option autoImplicit false

namespace MvPolynomial

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R]

/-- A polynomial in finitely many variables is regular as soon as one of its
actual coefficients is regular. This is the multivariate consequence of
McCoy's theorem used for polynomial extension of symbolic powers. -/
theorem fin_mem_nonZeroDivisors_of_coeff_mem (n : ℕ)
    (p : MvPolynomial (Fin n) R) (e : Fin n →₀ ℕ)
    (he : p.coeff e ∈ R⁰) : p ∈ (MvPolynomial (Fin n) R)⁰ := by
  induction n with
  | zero =>
    have hp : p = C (p.coeff e) := by
      ext d
      have hd : d = 0 := Subsingleton.elim _ _
      have he0 : e = 0 := Subsingleton.elim _ _
      simp [hd, he0]
    rw [hp]
    apply mem_nonZeroDivisors_iff_left.mpr
    intro q hq
    ext d
    apply (mem_nonZeroDivisors_iff_left.mp he)
    simpa using congrArg (fun f : MvPolynomial (Fin 0) R => f.coeff d) hq
  | succ n ih =>
    apply mem_nonZeroDivisors_of_injective (finSuccEquiv R n).injective
    apply Polynomial.mem_nonZeroDivisors_of_coeff_mem (e 0)
    apply ih _ (Finsupp.tail e)
    simpa only [finSuccEquiv_coeff_coeff, Finsupp.cons_tail] using he

/-- The finite-coordinate statement is independent of the enumeration of the
variables; no choice of a distinguished leading coefficient is required. -/
theorem mem_nonZeroDivisors_of_coeff_mem_finite {σ : Type*} [Fintype σ]
    (p : MvPolynomial σ R) (e : σ →₀ ℕ)
    (he : p.coeff e ∈ R⁰) : p ∈ (MvPolynomial σ R)⁰ := by
  classical
  let v := Fintype.equivFin σ
  apply mem_nonZeroDivisors_of_injective (renameEquiv R v).injective
  apply fin_mem_nonZeroDivisors_of_coeff_mem (Fintype.card σ) _ (e.mapDomain v)
  change (rename v p).coeff (e.mapDomain v) ∈ R⁰
  rwa [coeff_rename_mapDomain v v.injective]

end MvPolynomial

#print axioms MvPolynomial.mem_nonZeroDivisors_of_coeff_mem_finite
end

/- RECONSTRUCTED SOURCE SymbolicPolynomialExtension.lean -/
section

set_option autoImplicit false

noncomputable section

namespace FourPapers.Symmetric

open MvPolynomial
open scoped nonZeroDivisors

variable {R σ : Type*} [CommRing R]

theorem mv_map_quotient_eq_zero_iff (I : Ideal R) (f : MvPolynomial σ R) :
    MvPolynomial.map (Ideal.Quotient.mk I) f = 0 ↔
      f ∈ I.map (MvPolynomial.C : R →+* MvPolynomial σ R) := by
  rw [← RingHom.mem_ker, MvPolynomial.ker_map, Ideal.mk_ker]

theorem mv_comap_map_C (I : Ideal R) :
    (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)).comap MvPolynomial.C = I := by
  classical
  ext r
  rw [Ideal.mem_comap, MvPolynomial.mem_map_C_iff]
  constructor
  · intro h
    simpa using h 0
  · intro hr e
    by_cases he : e = 0
    · simpa [he] using hr
    · simp [MvPolynomial.coeff_C, he, Ne.symm he]

theorem mv_map_C_isPrime (P : Ideal R) [P.IsPrime] :
    (P.map (MvPolynomial.C : R →+* MvPolynomial σ R)).IsPrime := by
  have hker : P.map (MvPolynomial.C : R →+* MvPolynomial σ R) =
      RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk P) :
        MvPolynomial σ R →+* MvPolynomial σ (R ⧸ P)) := by
    rw [MvPolynomial.ker_map, Ideal.mk_ker]
  rw [hker]
  exact RingHom.ker_isPrime _

/-- Every element outside the prime acts regularly on each symbolic-power
quotient, directly from the denominator characterization. -/
theorem symbolicQuotient_mem_nonZeroDivisors (P : Ideal R) [P.IsPrime]
    (s : ℕ) {r : R} (hr : r ∉ P) :
    Ideal.Quotient.mk (symbolicPower P s) r ∈ (R ⧸ symbolicPower P s)⁰ := by
  apply mem_nonZeroDivisors_iff_left.mpr
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (mul_mem_symbolicPower_iff P s hr).mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [map_mul] using hx

/-- Extension to a polynomial ring remains saturated with respect to the
extended prime. A coefficient outside the prime is regular modulo the symbolic
power, so the whole denominator polynomial is regular by McCoy's theorem. -/
theorem symbolicPower_map_C_saturated [Fintype σ]
    (P : Ideal R) [P.IsPrime] (s : ℕ) (f g : MvPolynomial σ R)
    (hg : g ∉ P.map MvPolynomial.C)
    (hgf : g * f ∈ (symbolicPower P s).map MvPolynomial.C) :
    f ∈ (symbolicPower P s).map MvPolynomial.C := by
  classical
  have hcoeff : ∃ e, g.coeff e ∉ P := by
    simpa only [MvPolynomial.mem_map_C_iff, not_forall] using hg
  obtain ⟨e, he⟩ := hcoeff
  let φ := MvPolynomial.map (σ := σ) (Ideal.Quotient.mk (symbolicPower P s))
  have hregular : φ g ∈ (MvPolynomial σ (R ⧸ symbolicPower P s))⁰ := by
    apply MvPolynomial.mem_nonZeroDivisors_of_coeff_mem_finite _ e
    simpa only [φ, MvPolynomial.coeff_map] using
      symbolicQuotient_mem_nonZeroDivisors P s he
  apply (mv_map_quotient_eq_zero_iff (symbolicPower P s) f).mp
  apply (mem_nonZeroDivisors_iff_left.mp hregular)
  have hzero := (mv_map_quotient_eq_zero_iff (symbolicPower P s) (g * f)).mpr hgf
  simpa only [map_mul] using hzero

/-- True symbolic powers commute with adjoining any finite set of independent
polynomial variables. No Groebner presentation, characteristic, perfection, or
Noetherian hypothesis is used. -/
theorem symbolicPower_map_C [Fintype σ]
    (P : Ideal R) [P.IsPrime] (s : ℕ) :
    (symbolicPower P s).map (MvPolynomial.C : R →+* MvPolynomial σ R) =
      symbolicPower (P.map MvPolynomial.C) s := by
  letI := mv_map_C_isPrime (σ := σ) P
  apply le_antisymm
  · exact map_symbolicPower_le_of_comap MvPolynomial.C P (P.map MvPolynomial.C)
      (mv_comap_map_C P) le_rfl s
  · intro f hf
    obtain ⟨g, hg, hgf⟩ :=
      (mem_symbolicPower_iff (P.map MvPolynomial.C) s f).mp hf
    apply symbolicPower_map_C_saturated P s f g hg
    rw [← Ideal.map_pow] at hgf
    exact Ideal.map_mono (pow_le_symbolicPower P s) hgf

end FourPapers.Symmetric

#print axioms FourPapers.Symmetric.symbolicPower_map_C
end
end

/- RECONSTRUCTED SOURCE SymbolicHomogeneity.lean -/
section

set_option autoImplicit false

noncomputable section

namespace FourPapers.Symmetric

open MvPolynomial

variable {R σ κ : Type*} [CommRing R]

/-- Attach independent grading variables to every original variable. -/
def degreeTag (w : σ → κ →₀ ℕ) :
    MvPolynomial σ R →+* MvPolynomial κ (MvPolynomial σ R) :=
  eval₂Hom (MvPolynomial.C.comp MvPolynomial.C)
    (fun i => monomial (w i) (X i))

theorem degreeTag_monomial (w : σ → κ →₀ ℕ) (e : σ →₀ ℕ) (r : R) :
    degreeTag w (monomial e r) =
      monomial (Finsupp.weight w e) (monomial e r) := by
  classical
  simp only [degreeTag, eval₂Hom_monomial, RingHom.coe_comp, Function.comp_apply,
    monomial_pow, Finsupp.prod, ← monomial_sum_prod, C_mul_monomial]
  rw [Finsupp.weight_apply]
  congr 1
  rw [MvPolynomial.monomial_eq]
  rfl

/-- The coefficient at a grading monomial is exactly the independently defined
weighted homogeneous component. -/
theorem coeff_degreeTag (w : σ → κ →₀ ℕ) (f : MvPolynomial σ R) (d : κ →₀ ℕ) :
    (degreeTag w f).coeff d = weightedHomogeneousComponent w d f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => simp [map_add, hf, hg]
  | monomial e r =>
    rw [degreeTag_monomial, MvPolynomial.coeff_monomial]
    have hh := isWeightedHomogeneous_monomial w e r rfl
    by_cases hw : Finsupp.weight w e = d
    · subst d
      simp only [if_pos rfl]
      exact hh.weightedHomogeneousComponent_same.symm
    · simp only [if_neg hw]
      exact (hh.weightedHomogeneousComponent_ne d (Ne.symm hw)).symm

/-- Setting every grading variable to one recovers the original polynomial. -/
theorem eval_one_degreeTag (w : σ → κ →₀ ℕ) (f : MvPolynomial σ R) :
    MvPolynomial.eval (fun _ : κ => (1 : MvPolynomial σ R)) (degreeTag w f) = f := by
  have h : (MvPolynomial.eval (fun _ : κ => (1 : MvPolynomial σ R))).comp
      (degreeTag w) = RingHom.id (MvPolynomial σ R) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [degreeTag]
    · intro i
      simp [degreeTag, MvPolynomial.eval_monomial]
  exact RingHom.congr_fun h f

theorem degreeTag_comap_prime (w : σ → κ →₀ ℕ) (P : Ideal (MvPolynomial σ R))
    (hP : ∀ f ∈ P, ∀ d, weightedHomogeneousComponent w d f ∈ P) :
    (P.map MvPolynomial.C).comap (degreeTag w) = P := by
  classical
  ext f
  constructor
  · intro hf
    have hev : (P.map (MvPolynomial.C : MvPolynomial σ R →+*
        MvPolynomial κ (MvPolynomial σ R))).map
        (MvPolynomial.eval (fun _ : κ => (1 : MvPolynomial σ R))) = P := by
      rw [Ideal.map_map]
      have hec : (MvPolynomial.eval (fun _ : κ => (1 : MvPolynomial σ R))).comp
          MvPolynomial.C = RingHom.id (MvPolynomial σ R) := by
        apply RingHom.ext
        intro r
        simp
      rw [hec, Ideal.map_id]
    have h := Ideal.mem_map_of_mem
      (MvPolynomial.eval (fun _ : κ => (1 : MvPolynomial σ R)))
      (show degreeTag w f ∈ P.map MvPolynomial.C from hf)
    rw [hev, eval_one_degreeTag] at h
    exact h
  · intro hf
    change degreeTag w f ∈ P.map MvPolynomial.C
    rw [MvPolynomial.mem_map_C_iff]
    intro d
    rw [coeff_degreeTag]
    exact hP f hf d

/-- Symbolic powers of a multihomogeneous prime are multihomogeneous. This
proof uses an honest polynomial extension and coefficient extraction, and so
works over finite fields and in arbitrary characteristic. -/
theorem symbolicPower_weightedHomogeneousComponent [Fintype κ]
    (w : σ → κ →₀ ℕ) (P : Ideal (MvPolynomial σ R)) [P.IsPrime]
    (hP : ∀ f ∈ P, ∀ d, weightedHomogeneousComponent w d f ∈ P)
    (s : ℕ) {f : MvPolynomial σ R} (hf : f ∈ symbolicPower P s) (d : κ →₀ ℕ) :
    weightedHomogeneousComponent w d f ∈ symbolicPower P s := by
  letI := mv_map_C_isPrime (σ := κ) P
  have hc := degreeTag_comap_prime w P hP
  have hm : P.map (degreeTag w) ≤ P.map MvPolynomial.C := by
    rw [Ideal.map_le_iff_le_comap, hc]
  have h := map_symbolicPower_le_of_comap (degreeTag w) P (P.map MvPolynomial.C)
    hc hm s (Ideal.mem_map_of_mem (degreeTag w) hf)
  rw [← symbolicPower_map_C (σ := κ) P s, MvPolynomial.mem_map_C_iff] at h
  simpa only [coeff_degreeTag] using h d

end FourPapers.Symmetric

#print axioms FourPapers.Symmetric.symbolicPower_weightedHomogeneousComponent
end
end

/- RECONSTRUCTED SOURCE MatrixMinorIdeals.lean -/
section

set_option autoImplicit false

/-!
# Determinantal ideals under invertible row and column operations

All matrix dimensions and all minor sizes are arbitrary. We first allow arbitrary index
maps in a minor: repetitions contribute zero and permutations only change its sign.
The rectangular determinant expansion below is adapted, with its proof retained, from
`TauCeti.LinearAlgebra.Matrix.Divisibility`, commit
`06d5bb4e3ebb737dc6538567f5c53bf8800b9362` (Apache-2.0; see `Vendor/LICENSE`).
-/

noncomputable section

namespace FourPapers.Symmetric

open Matrix Finset

variable {R l m n o : Type*} [CommRing R]

/-- The ideal of all minors of a fixed size. Arbitrary index maps are permitted. -/
def matrixMinorIdeal (M : Matrix m n R) (t : ℕ) : Ideal R :=
  Ideal.span {x | ∃ a : Fin t → m, ∃ b : Fin t → n, x = (M.submatrix a b).det}

theorem det_submatrix_mem_matrixMinorIdeal (M : Matrix m n R) (t : ℕ)
    (a : Fin t → m) (b : Fin t → n) : (M.submatrix a b).det ∈ matrixMinorIdeal M t :=
  Ideal.subset_span ⟨a, b, rfl⟩

/-- Determinantal ideals commute with every coefficient-ring homomorphism. -/
theorem matrixMinorIdeal_map {S : Type*} [CommRing S] (φ : R →+* S)
    (M : Matrix m n R) (t : ℕ) :
    (matrixMinorIdeal M t).map φ = matrixMinorIdeal (M.map φ) t := by
  rw [matrixMinorIdeal, Ideal.map_span, matrixMinorIdeal]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, b, rfl⟩, rfl⟩
    refine ⟨a, b, ?_⟩
    rw [RingHom.map_det]
    rfl
  · rintro ⟨a, b, rfl⟩
    refine ⟨(M.submatrix a b).det, ⟨a, b, rfl⟩, ?_⟩
    rw [RingHom.map_det]
    rfl

/-- Multilinearity expands a determinant of a rectangular product into minors of the
right factor. No field or domain hypothesis is used. -/
theorem determinant_product_expansion {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype m] (A : Matrix ι m R) (B : Matrix m ι R) :
    (A * B).det = ∑ f : ι → m, (∏ i, A i (f i)) * (B.submatrix f id).det := by
  classical
  have hrows : (A * B : ι → ι → R) = fun i => ∑ j, A i j • (B j : ι → R) := by
    ext i k
    simp [Matrix.mul_apply, Finset.sum_apply]
  have hsum := (detRowAlternating (R := R) (n := ι)).toMultilinearMap.map_sum
    (fun i j => A i j • (B j : ι → R))
  simp only [AlternatingMap.coe_multilinearMap, MultilinearMap.map_smul_univ] at hsum
  rw [Matrix.det, hrows, hsum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [smul_eq_mul, Matrix.det]
  congr 2

/-- Left multiplication cannot enlarge a fixed-size minors ideal. -/
theorem matrixMinorIdeal_mul_left_le [Fintype m]
    (P : Matrix l m R) (M : Matrix m n R) (t : ℕ) :
    matrixMinorIdeal (P * M) t ≤ matrixMinorIdeal M t := by
  classical
  apply Ideal.span_le.mpr
  rintro _ ⟨a, b, rfl⟩
  rw [Matrix.submatrix_mul P M a id b Function.bijective_id,
    determinant_product_expansion]
  apply (matrixMinorIdeal M t).sum_mem
  intro f _
  apply (matrixMinorIdeal M t).mul_mem_left
  exact det_submatrix_mem_matrixMinorIdeal M t f b

/-- Transposing a matrix does not change its fixed-size minors ideal. -/
theorem matrixMinorIdeal_transpose (M : Matrix m n R) (t : ℕ) :
    matrixMinorIdeal M.transpose t = matrixMinorIdeal M t := by
  have hle (A : Matrix m n R) : matrixMinorIdeal A.transpose t ≤ matrixMinorIdeal A t := by
    apply Ideal.span_le.mpr
    rintro _ ⟨a, b, rfl⟩
    rw [← Matrix.transpose_submatrix, Matrix.det_transpose]
    exact det_submatrix_mem_matrixMinorIdeal A t b a
  apply le_antisymm (hle M)
  have hle' : matrixMinorIdeal M t ≤ matrixMinorIdeal M.transpose t := by
    apply Ideal.span_le.mpr
    rintro _ ⟨a, b, rfl⟩
    change (M.submatrix a b).det ∈ matrixMinorIdeal M.transpose t
    have h := det_submatrix_mem_matrixMinorIdeal M.transpose t b a
    simpa only [← Matrix.transpose_submatrix, Matrix.det_transpose] using h
  exact hle'

/-- Right multiplication cannot enlarge a fixed-size minors ideal. -/
theorem matrixMinorIdeal_mul_right_le [Fintype n]
    (M : Matrix m n R) (Q : Matrix n o R) (t : ℕ) :
    matrixMinorIdeal (M * Q) t ≤ matrixMinorIdeal M t := by
  rw [← matrixMinorIdeal_transpose (M * Q), Matrix.transpose_mul,
    ← matrixMinorIdeal_transpose M]
  exact matrixMinorIdeal_mul_left_le Q.transpose M.transpose t

/-- Two-sided multiplication preserves all determinantal containments. -/
theorem matrixMinorIdeal_mul_mul_le [Fintype m] [Fintype n]
    (P : Matrix l m R) (M : Matrix m n R) (Q : Matrix n o R) (t : ℕ) :
    matrixMinorIdeal (P * M * Q) t ≤ matrixMinorIdeal M t :=
  (matrixMinorIdeal_mul_right_le (P * M) Q t).trans
    (matrixMinorIdeal_mul_left_le P M t)

/-- Invertible row and column operations preserve every determinantal ideal exactly. -/
theorem matrixMinorIdeal_units_mul [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (P : (Matrix m m R)ˣ) (M : Matrix m n R) (Q : (Matrix n n R)ˣ) (t : ℕ) :
    matrixMinorIdeal ((P : Matrix m m R) * M * (Q : Matrix n n R)) t =
      matrixMinorIdeal M t := by
  apply le_antisymm (matrixMinorIdeal_mul_mul_le _ _ _ _)
  have h := matrixMinorIdeal_mul_mul_le (P⁻¹ : (Matrix m m R)ˣ).val
    ((P : Matrix m m R) * M * (Q : Matrix n n R)) (Q⁻¹ : (Matrix n n R)ˣ).val t
  have hback : (P⁻¹ : (Matrix m m R)ˣ).val *
      ((P : Matrix m m R) * M * (Q : Matrix n n R)) *
      (Q⁻¹ : (Matrix n n R)ˣ).val = M := by
    calc
      _ = ((P⁻¹ : (Matrix m m R)ˣ).val * (P : Matrix m m R)) * M *
          ((Q : Matrix n n R) * (Q⁻¹ : (Matrix n n R)ˣ).val) := by
        simp only [Matrix.mul_assoc]
      _ = M := by simp
  simpa only [hback] using h

theorem matrixMinorIdeal_mul_mul_of_isUnit [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (P : Matrix m m R) (M : Matrix m n R)
    (Q : Matrix n n R) (hP : IsUnit P) (hQ : IsUnit Q) (t : ℕ) :
    matrixMinorIdeal (P * M * Q) t = matrixMinorIdeal M t := by
  obtain ⟨P, rfl⟩ := hP
  obtain ⟨Q, rfl⟩ := hQ
  exact matrixMinorIdeal_units_mul P M Q t

/-- Relabeling the entire row and column index sets preserves the minors ideal. -/
theorem matrixMinorIdeal_submatrix_equiv {m' n' : Type*}
    (M : Matrix m n R) (e : m' ≃ m) (f : n' ≃ n) (t : ℕ) :
    matrixMinorIdeal (M.submatrix e f) t = matrixMinorIdeal M t := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, b, rfl⟩
    exact det_submatrix_mem_matrixMinorIdeal M t (e ∘ a) (f ∘ b)
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, b, rfl⟩
    change (M.submatrix a b).det ∈ matrixMinorIdeal (M.submatrix e f) t
    have h := det_submatrix_mem_matrixMinorIdeal (M.submatrix e f) t
      (e.symm ∘ a) (f.symm ∘ b)
    simpa only [Matrix.submatrix_submatrix, Function.comp_def,
      Equiv.apply_symm_apply] using h

/-- Every injective finite index list is an increasing list followed by a permutation.
This identifies the arbitrary-map minor convention with the paper's increasing lists. -/
theorem exists_orderEmbedding_perm {a t : ℕ} (f : Fin t → Fin a)
    (hf : Function.Injective f) :
    ∃ (u : Fin t ↪o Fin a) (σ : Equiv.Perm (Fin t)), ∀ i, u (σ i) = f i := by
  classical
  let s : Finset (Fin a) := univ.image f
  have hs : s.card = t := by
    simpa only [s, Finset.card_univ, Fintype.card_fin] using
      Finset.card_image_of_injective univ hf
  let g : Fin t → s := fun i => ⟨f i, mem_image.mpr ⟨i, mem_univ i, rfl⟩⟩
  have hg : Function.Bijective g := by
    constructor
    · intro i j hij
      exact hf (congrArg Subtype.val hij)
    · rintro ⟨x, hx⟩
      obtain ⟨i, _, hi⟩ := mem_image.mp hx
      exact ⟨i, Subtype.ext hi⟩
  let e : Fin t ≃ s := Equiv.ofBijective g hg
  let v : Fin t ≃o s := s.orderIsoOfFin hs
  refine ⟨s.orderEmbOfFin hs, e.trans v.symm.toEquiv, ?_⟩
  intro i
  change (v (v.symm (e i))).val = f i
  rw [v.apply_symm_apply]
  rfl

/-- Fixed-size minors with the paper's strictly increasing lists. -/
def orderedMatrixMinorIdeal {a b : ℕ} (M : Matrix (Fin a) (Fin b) R) (t : ℕ) : Ideal R :=
  Ideal.span {x | ∃ u : Fin t ↪o Fin a, ∃ v : Fin t ↪o Fin b,
    x = (M.submatrix u v).det}

/-- Allowing all index maps adds no generators to the ideal: repeated rows/columns vanish,
and sorting the remaining rows/columns changes only the determinant sign. -/
theorem matrixMinorIdeal_eq_ordered {a b : ℕ} (M : Matrix (Fin a) (Fin b) R) (t : ℕ) :
    matrixMinorIdeal M t = orderedMatrixMinorIdeal M t := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨f, g, rfl⟩
    by_cases hf : Function.Injective f
    · by_cases hg : Function.Injective g
      · obtain ⟨u, σ, hσ⟩ := exists_orderEmbedding_perm f hf
        obtain ⟨v, τ, hτ⟩ := exists_orderEmbedding_perm g hg
        have hM : M.submatrix f g =
            ((M.submatrix u v).submatrix σ id).submatrix id τ := by
          ext i j
          simp only [Matrix.submatrix_apply, id_eq, hσ, hτ]
        rw [hM, Matrix.det_permute', Matrix.det_permute]
        apply (orderedMatrixMinorIdeal M t).mul_mem_left
        apply (orderedMatrixMinorIdeal M t).mul_mem_left
        exact Ideal.subset_span ⟨u, v, rfl⟩
      · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hg
        rw [Matrix.det_zero_of_column_eq hne (fun k => by simp [hij])]
        exact Ideal.zero_mem _
    · obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hf
      rw [Matrix.det_zero_of_row_eq hne (by ext k; simp [hij])]
      exact Ideal.zero_mem _
  · apply Ideal.span_le.mpr
    rintro _ ⟨u, v, rfl⟩
    exact det_submatrix_mem_matrixMinorIdeal M t u v

end FourPapers.Symmetric
end
end

/- RECONSTRUCTED SOURCE RankMinors.lean -/
section

set_option autoImplicit false

/-!
# Matrix rank detected by actual minors

The field argument is adapted with its proof retained from
`TauCeti.LinearAlgebra.Matrix.Rank`, commit
`06d5bb4e3ebb737dc6538567f5c53bf8800b9362` (Apache-2.0).
The construction chooses independent rows and then independent columns. No rank
criterion is imported as an unverified assertion.
-/

noncomputable section

namespace FourPapers.Symmetric

open Matrix

 theorem independent_rows_iff_nonzero_minor {m n K : Type*} [Fintype m]
    [DecidableEq m] [Finite n] [Field K] {A : Matrix m n K} :
    LinearIndependent K A.row ↔ ∃ e : m ↪ n, (A.submatrix id e).det ≠ 0 := by
  have : Fintype n := Fintype.ofFinite n
  refine ⟨fun h => ?_, fun ⟨e, he⟩ => ?_⟩
  · obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.col
    have : Finite κ := Finite.of_injective a ha
    have : Fintype κ := Fintype.ofFinite κ
    have hcard : Fintype.card m = Fintype.card κ := by
      rw [linearIndependent_iff_card_eq_finrank_span.1 hli, Set.finrank, hspan,
        ← rank_eq_finrank_span_cols, h.rank_matrix]
    let e : m ↪ n := (Fintype.equivOfCardEq hcard).toEmbedding.trans ⟨a, ha⟩
    have hcol : LinearIndependent K (A.submatrix id e).col :=
      hli.comp _ (Fintype.equivOfCardEq hcard).injective
    exact ⟨e, ((isUnit_iff_isUnit_det _).1 (linearIndependent_col_iff_isUnit.1 hcol)).ne_zero⟩
  · exact LinearIndependent.of_comp (LinearMap.funLeft K K e)
      (linearIndependent_rows_of_det_ne_zero he)

 theorem le_rank_iff_nonzero_minor {m n K : Type*} [Field K] [Finite m] [Fintype n]
    {A : Matrix m n K} {p : ℕ} :
    p ≤ A.rank ↔ ∃ (r : Fin p ↪ m) (c : Fin p ↪ n), (A.submatrix r c).det ≠ 0 := by
  refine ⟨fun hp => ?_, fun ⟨r, c, h⟩ => ?_⟩
  · obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.row
    have : Finite κ := Finite.of_injective a ha
    have : Fintype κ := Fintype.ofFinite κ
    have hcard : A.rank = Fintype.card κ := by
      rw [linearIndependent_iff_card_eq_finrank_span.1 hli, Set.finrank, hspan,
        rank_eq_finrank_span_row]
    let r : Fin p ↪ m :=
      ((Fin.castLEEmb (hcard ▸ hp)).trans (Fintype.equivFin κ).symm.toEmbedding).trans ⟨a, ha⟩
    have hr : LinearIndependent K (A.submatrix r id).row :=
      hli.comp _ (Fin.castLEEmb _ |>.trans (Fintype.equivFin κ).symm.toEmbedding).injective
    obtain ⟨c, hc⟩ := independent_rows_iff_nonzero_minor.1 hr
    exact ⟨r, c, by rwa [submatrix_submatrix] at hc⟩
  · classical
    simpa [rank_of_det_ne_zero h] using rank_submatrix_le A r c

/-- The vanishing-minor characterization retains every rectangular dimension and
all rank bounds, including bounds larger than either dimension. -/
theorem rank_le_iff_vanishing_minors {m n K : Type*} [Field K] [Finite m] [Fintype n]
    {A : Matrix m n K} {p : ℕ} :
    A.rank ≤ p ↔ ∀ (r : Fin (p + 1) ↪ m) (c : Fin (p + 1) ↪ n),
      (A.submatrix r c).det = 0 := by
  rw [← not_lt, Nat.lt_iff_add_one_le, le_rank_iff_nonzero_minor]
  simp only [not_exists, ne_eq, not_not]

end FourPapers.Symmetric
end
end

/- RECONSTRUCTED SOURCE RankGeometry.lean -/
section

set_option autoImplicit false

/-!
# Actual northwest rank loci and their determinantal equations

The point set is defined by ranks of actual matrices. Its equality with the zero
set of the prescribed minor ideal is proved by the rectangular rank/minor theorem.
The Nullstellensatz consequence is explicitly conditional on the separately needed
primality proof; it is not a proof of that primality assertion.
-/

noncomputable section

open MvPolynomial Matrix

namespace FourPapers.Symmetric

universe u v

/-- Northwest ranks of an actual matrix. A prefix ending at `i : Fin n` includes
all indices at most `i`; no artificial bound on a matrix rank is imposed. -/
def matrixRankArray {n : ℕ} {F : Type u} [Field F]
    (w : Matrix (Fin n) (Fin n) F) : RankArray n :=
  fun i j => (w.submatrix (fun p : {p : Fin n // p ≤ i} => p.val)
    (fun q : {q : Fin n // q ≤ j} => q.val)).rank

/-- Actual symmetric matrices satisfying all northwest rank inequalities,
identified with their independent folded coordinates. -/
def rankBoundLocus {n : ℕ} (K : Type v) [Field K] (r : RankArray n) :
    Set (Entry n → K) :=
  {x | ∀ i j, matrixRankArray (fun a b => x (fold a b)) i j ≤ r i j}

 theorem aeval_minor {n t : ℕ} {K : Type v} [CommRing K]
    (x : Entry n → K) (a b : Fin t ↪o Fin n) :
    aeval x (minor K a b) = Matrix.det (Matrix.of (fun p q => x (fold (a p) (b q)))) := by
  change (aeval x).toRingHom (((genericMatrix n K).submatrix a b).det) = _
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [genericMatrix, Matrix.submatrix_apply]

/-- Every point of the determinantal zero set satisfies the actual rank bounds,
and every matrix with those rank bounds annihilates the prescribed ideal. -/
theorem zeroLocus_northwestIdeal {n : ℕ} {K : Type v} [Field K] (r : RankArray n) :
    MvPolynomial.zeroLocus K (northwestIdeal K r) = rankBoundLocus K r := by
  classical
  rw [northwestIdeal, MvPolynomial.zeroLocus_span]
  ext x
  constructor
  · intro hx
    intro i j
    apply rank_le_iff_vanishing_minors.mpr
    intro a b
    let f : Fin (r i j + 1) → Fin n := fun p => (a p).val
    let g : Fin (r i j + 1) → Fin n := fun p => (b p).val
    have hf : Function.Injective f := fun p q h => a.injective (Subtype.ext h)
    have hg : Function.Injective g := fun p q h => b.injective (Subtype.ext h)
    obtain ⟨u, σ, hσ⟩ := exists_orderEmbedding_perm f hf
    obtain ⟨v, τ, hτ⟩ := exists_orderEmbedding_perm g hg
    have hu : ∀ p, u p ≤ i := by
      intro p
      have hp := hσ (σ.symm p)
      rw [σ.apply_symm_apply] at hp
      rw [hp]
      exact (a (σ.symm p)).property
    have hv : ∀ p, v p ≤ j := by
      intro p
      have hp := hτ (τ.symm p)
      rw [τ.apply_symm_apply] at hp
      rw [hp]
      exact (b (τ.symm p)).property
    have hz := hx (minor K u v) ⟨i, j, u, v, hu, hv, rfl⟩
    rw [aeval_minor] at hz
    have hM :
        ((Matrix.submatrix (Matrix.of (fun a b => x (fold a b)))
          (fun p : {p : Fin n // p ≤ i} => p.val)
          (fun q : {q : Fin n // q ≤ j} => q.val)).submatrix a b) =
          Matrix.submatrix (Matrix.submatrix (Matrix.of (fun p q => x (fold (u p) (v q)))) σ id) id τ := by
      ext p q
      change x (fold (f p) (g q)) = x (fold (u (σ p)) (v (τ q)))
      rw [hσ, hτ]
    change (((Matrix.of (fun a b => x (fold a b))).submatrix
      (fun p : {p : Fin n // p ≤ i} => p.val)
      (fun q : {q : Fin n // q ≤ j} => q.val)).submatrix a b).det = 0
    rw [hM, Matrix.det_permute', Matrix.det_permute, hz, mul_zero, mul_zero]
  · intro hx
    rintro f ⟨i, j, a, b, ha, hb, rfl⟩
    let a' : Fin (r i j + 1) ↪ {p : Fin n // p ≤ i} :=
      ⟨fun p => ⟨a p, ha p⟩, fun p q h => a.injective (congrArg Subtype.val h)⟩
    let b' : Fin (r i j + 1) ↪ {p : Fin n // p ≤ j} :=
      ⟨fun p => ⟨b p, hb p⟩, fun p q h => b.injective (congrArg Subtype.val h)⟩
    rw [aeval_minor]
    exact rank_le_iff_vanishing_minors.mp (hx i j) a' b'

/-- The exact algebraically closed defining-ideal consequence, once the independent
prime-ideal theorem has been established. -/
theorem vanishingIdeal_rankBoundLocus_of_prime {n : ℕ} {K : Type v}
    [Field K] [IsAlgClosed K] (r : RankArray n)
    (hprime : (northwestIdeal K r).IsPrime) :
    MvPolynomial.vanishingIdeal K (rankBoundLocus K r) = northwestIdeal K r := by
  letI : (northwestIdeal K r).IsPrime := hprime
  rw [← zeroLocus_northwestIdeal r]
  exact MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (northwestIdeal K r)

end FourPapers.Symmetric
end
end

/- RECONSTRUCTED SOURCE SchurCoordinates.lean -/
section

set_option autoImplicit false

/-!
# The Schur change is a polynomial coordinate equivalence

The carrier variables and residual symmetric variables are independent. Translating every
residual variable by a polynomial in the carriers is an algebra automorphism. The diagonal
Schur substitution is the instance `Cᵢⱼ ↦ Cᵢⱼ - x⁻¹ bᵢ bⱼ` over the ring in which the pivot
has been inverted. Both directions are explicitly checked below.
-/

noncomputable section

namespace FourPapers.Symmetric

open MvPolynomial

section Translation

variable {σ τ R : Type*} [CommRing R]

/-- A triangular coordinate substitution fixing the first family of variables. -/
noncomputable def triangularShift (f : τ → MvPolynomial σ R) :
    MvPolynomial (σ ⊕ τ) R →ₐ[R] MvPolynomial (σ ⊕ τ) R :=
  aeval (fun i => match i with
    | .inl a => X (.inl a)
    | .inr b => X (.inr b) + rename Sum.inl (f b))

@[simp] theorem triangularShift_C (f : τ → MvPolynomial σ R) (r : R) :
    triangularShift f (C r) = C r := by
  simp [triangularShift]

@[simp] theorem triangularShift_X_left (f : τ → MvPolynomial σ R) (i : σ) :
    triangularShift f (X (.inl i)) = X (.inl i) := by
  simp [triangularShift]

@[simp] theorem triangularShift_X_right (f : τ → MvPolynomial σ R) (i : τ) :
    triangularShift f (X (.inr i)) = X (.inr i) + rename Sum.inl (f i) := by
  simp [triangularShift]

/-- Every polynomial in the carriers is fixed, not only the individual carrier variables. -/
@[simp] theorem triangularShift_rename (f : τ → MvPolynomial σ R)
    (p : MvPolynomial σ R) :
    triangularShift f (rename Sum.inl p) = rename Sum.inl p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- Composing shifts adds their translation polynomials. -/
theorem triangularShift_comp (f g : τ → MvPolynomial σ R) :
    (triangularShift f).comp (triangularShift g) = triangularShift (f + g) := by
  ext i
  cases i with
  | inl i => simp
  | inr i => simp [add_assoc, add_comm, add_left_comm]

@[simp] theorem triangularShift_zero :
    triangularShift (0 : τ → MvPolynomial σ R) =
      AlgHom.id R (MvPolynomial (σ ⊕ τ) R) := by
  ext i
  cases i <;> simp

/-- The inverse is translation by the negatives of exactly the same polynomials. -/
noncomputable def triangularShiftEquiv (f : τ → MvPolynomial σ R) :
    MvPolynomial (σ ⊕ τ) R ≃ₐ[R] MvPolynomial (σ ⊕ τ) R :=
  AlgEquiv.ofAlgHom (triangularShift f) (triangularShift (-f))
    (by rw [triangularShift_comp, add_neg_cancel, triangularShift_zero])
    (by rw [triangularShift_comp, neg_add_cancel, triangularShift_zero])

@[simp] theorem triangularShiftEquiv_apply (f : τ → MvPolynomial σ R)
    (p : MvPolynomial (σ ⊕ τ) R) :
    triangularShiftEquiv f p = triangularShift f p := rfl

end Translation

section SymmetricSchur

variable {n : ℕ} {R : Type*} [CommRing R]

/-- Variables after singling out the first row: carriers and residual symmetric entries. -/
abbrev PivotVariables (n : ℕ) := Fin n ⊕ Entry n

/-- The polynomial offset in a diagonal Schur coordinate. -/
def schurOffset (q : R) (e : Entry n) : MvPolynomial (Fin n) R :=
  -(C q * X e.val.1 * X e.val.2)

/-- The Schur coordinate equivalence for a supplied inverse pivot `q`. The equivalence
itself exists for every `q`; its interpretation as elimination additionally uses `x*q=1`. -/
noncomputable def schurCoordinateEquiv (q : R) :
    MvPolynomial (PivotVariables n) R ≃ₐ[R] MvPolynomial (PivotVariables n) R :=
  triangularShiftEquiv (schurOffset q)

@[simp] theorem schurCoordinateEquiv_carrier (q : R) (i : Fin n) :
    schurCoordinateEquiv q (X (.inl i)) = X (.inl i) := by
  simp [schurCoordinateEquiv]

/-- Every residual coordinate has exactly the Schur-complement value. -/
@[simp] theorem schurCoordinateEquiv_entry (q : R) (i j : Fin n) :
    schurCoordinateEquiv q (X (.inr (fold i j))) =
      X (.inr (fold i j)) - C q * X (.inl i) * X (.inl j) := by
  simp only [schurCoordinateEquiv, triangularShiftEquiv_apply,
    triangularShift_X_right, schurOffset, map_neg, map_mul, rename_C, rename_X]
  by_cases hij : i ≤ j
  · simp [fold, toLex, Equiv.refl_apply, max_eq_right hij, min_eq_left hij, sub_eq_add_neg, mul_comm, mul_left_comm]
    change X (Sum.inl j) * (X (Sum.inl i) * C q) = X (Sum.inl i) * (X (Sum.inl j) * C q)
    ring
  · simp [fold, toLex, Equiv.refl_apply, max_eq_left (le_of_not_ge hij), min_eq_right (le_of_not_ge hij),
      sub_eq_add_neg]
    rfl

end SymmetricSchur

end FourPapers.Symmetric
end
end

namespace FourPapers.Symmetric
universe u v
/-- The algebraic assertions of Theorem 1.1, with unrelated realization and
coefficient fields and no rank-size restriction. -/
def RankLocusAssertion : Prop :=
  ∀ (n : ℕ) (F : Type u) [Field F] (w : Matrix (Fin n) (Fin n) F),
    w.transpose = w →
    ∀ (K : Type v) [Field K],
      (northwestIdeal K (matrixRankArray w)).IsPrime ∧
      initialIdeal K (northwestIdeal K (matrixRankArray w)) =
        northwestAntidiagonalIdeal K (matrixRankArray w)

/-- The geometric conclusion of Theorem 1.1 uses the vanishing ideal of the
actual rank-bounded set over an algebraically closed field. In particular, it is
not encoded by defining the rank locus to be the zero locus of the desired ideal. -/
def RankDefiningIdealAssertion : Prop :=
  ∀ (n : ℕ) (F : Type u) [Field F] (w : Matrix (Fin n) (Fin n) F),
    w.transpose = w →
    ∀ (K : Type v) [Field K] [IsAlgClosed K],
      MvPolynomial.vanishingIdeal K (rankBoundLocus K (matrixRankArray w)) =
        northwestIdeal K (matrixRankArray w)

/-- Complete target for Theorem 1.1, including its algebraically closed
rank-locus conclusion. This conjunction is a statement target, not a proof. -/
def SymmetricRankLociTheorem : Prop :=
  RankLocusAssertion.{u, v} ∧ RankDefiningIdealAssertion.{u, v}


end FourPapers.Symmetric
#print axioms FourPapers.Symmetric.symbolicPower_map_C
#print axioms FourPapers.Symmetric.symbolicPower_weightedHomogeneousComponent
#print axioms FourPapers.Symmetric.zeroLocus_northwestIdeal
#print axioms FourPapers.Symmetric.vanishingIdeal_rankBoundLocus_of_prime
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let constants := env.checked.get.constants.foldStage2
    (fun acc name ci => acc.push (name, ci)) (#[] : Array (Name × ConstantInfo))
  for (name, ci) in constants do
    if ci.isAxiom || ci.isUnsafe || ci.isPartial then
      throwError "Unapproved local declaration: {name}"
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let roots : Array Name := #[`FourPapers.Symmetric.symbolicGenerators_one_groebner, `FourPapers.Symmetric.mixedGroebner_of_positiveBounds, `FourPapers.Symmetric.mixedGroebner_cons_one, `FourPapers.Symmetric.integralBaseChangeAssertion_of_compatible, `FourPapers.Symmetric.symbolicPower_map_coeff_of_fraction_groebner, `FourPapers.Symmetric.symbolicPower_comap_chart, `MonomialOrder.ideal_eq_of_le_of_initial_le, `FourPapers.Symmetric.Reduction.positiveCore_implies_compatible, `FourPapers.Symmetric.Reduction.positiveCore_implies_integral, `Multisegment.sum_colLen_dualInsertionShape_eq_listWordGreeneMax, `FourPapers.Symmetric.symbolicPower_map_C, `FourPapers.Symmetric.symbolicPower_weightedHomogeneousComponent, `FourPapers.Symmetric.zeroLocus_northwestIdeal, `FourPapers.Symmetric.vanishingIdeal_rankBoundLocus_of_prime]
  for root in roots do
    let axs ← collectAxioms root
    for ax in axs do
      if !allowed.contains ax then
        throwError "Unapproved axiom in {root}: {ax}"
  let ctors (ci : ConstantInfo) : Array Name :=
    match ci with
    | .inductInfo v => v.ctors.toArray
    | _ => #[]
  let mut names : NameSet := {}
  for (name, ci) in constants do
    names := names.insert name
    for dep in ci.type.getUsedConstants do
      names := names.insert dep
    for dep in (ci.value? true).map Expr.getUsedConstants |>.getD #[] do
      names := names.insert dep
    for dep in ctors ci do
      names := names.insert dep
  let dictionary := names.toArray.qsort Name.lt
  let mut indices : NameMap Nat := {}
  for i in [:dictionary.size] do
    indices := indices.insert dictionary[i]! i
  let index (n : Name) := (indices.find? n).getD 0
  let data := constants.map fun (name, ci) =>
    let typeDeps := ci.type.getUsedConstants
    let valueDeps := (ci.value? true).map Expr.getUsedConstants |>.getD #[]
    Json.arr #[toJson (index name), toJson (typeDeps.map index),
      toJson (valueDeps.map index), toJson ((ctors ci).map index),
      toJson ci.isAxiom, toJson ci.isUnsafe, toJson ci.isPartial]
  let graph := Json.mkObj [
    ("format", toJson "local-proof-dag-v1"),
    ("columns", toJson (#["name", "type", "value", "inductiveCtors", "axiom", "unsafe", "partial"] : Array String)),
    ("names", toJson (dictionary.map Name.toString)),
    ("nodes", Json.arr data),
    ("roots", toJson (roots.map index))]
  logInfo m!"DEPENDENCY_GRAPH {Json.compress graph}"
  logInfo m!"AUDIT_OK {constants.size} local declarations; {roots.size} roots; no local axioms, unsafe or partial declarations."
