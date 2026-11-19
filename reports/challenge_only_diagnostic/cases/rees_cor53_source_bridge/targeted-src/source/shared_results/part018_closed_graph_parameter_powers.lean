module
public import graph_foundation.part013
public import shared_results.part018_rees_standard_identification

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphParameterPowers -/
section

/-! # Monic Gröbner bases for every power of the graph parameter ideal

The first initial ideal is identified with the literal two-row sublattice
ideal. Over the fraction field, the proved all-power initial-ideal theorem
makes every product set a Gröbner basis. Since the products are monic, the
injective-coefficient-map theorem descends that Gröbner basis back to the
original domain. In particular this applies to the actual ring `ℤ[z]`.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
noncomputable section

namespace FourPapers.Sublattice
open Classical MvPolynomial CommAlg.Polymatroid
open scoped Pointwise
universe u
variable {N : ℕ} {R : Type u} [CommRing R] [IsDomain R]

private lemma intervalLabeling_closed_for_parameter_powers
    {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G) : ClosedLabeling G := by
  constructor
  · intro a b c hab hac hbc habG hacG
    rcases lt_or_gt_of_ne hbc with hbc | hcb
    · exact (hG a b c hab hbc hacG).2
    · exact ((hG a c b hac hcb habG).2).symm
  · intro a b c hac hbc hab hacG hbcG
    rcases lt_or_gt_of_ne hab with hab | hba
    · exact (hG a b c hab hbc hacG).1
    · exact ((hG b a c hba hac hbcG).1).symm

theorem graphParameterProducts_leadingCoeff (t : R) (ht : t ≠ 0)
    (G : SimpleGraph (Fin N)) (s : ℕ) :
    ∀ f ∈ graphParameterGenerators t G ^ s, graphLexOrder.leadingCoeff f = 1 := by
  induction s with
  | zero =>
      intro f hf
      have hf' : f = 1 := by simpa only [pow_zero, Set.mem_one] using hf
      rw [hf', MonomialOrder.leadingCoeff_one]
  | succ s ih =>
      intro f hf
      rw [pow_succ] at hf
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hf
      obtain ⟨i, j, hij, _, rfl⟩ := hb
      rw [MonomialOrder.leadingCoeff_mul, ih a ha,
        graphParameterBinomial_leadingCoeff t ht hij, one_mul]

theorem graphParameterProducts_unit_leading (t : R) (ht : t ≠ 0)
    (G : SimpleGraph (Fin N)) (s : ℕ) :
    ∀ f ∈ graphParameterGenerators t G ^ s, f ≠ 0 →
      IsUnit (graphLexOrder.leadingCoeff f) := by
  intro f hf _
  rw [graphParameterProducts_leadingCoeff t ht G s f hf]
  exact isUnit_one

lemma weight_le_of_strict_monomial_tail {V : Type*} (w : V → ℕ)
    (f : MvPolynomial V R) (a : V →₀ ℕ)
    (htail : ∀ b ∈ (monomial a (1 : R) - f).support,
      Finsupp.weight w b < Finsupp.weight w a)
    (b : V →₀ ℕ) (hb : b ∈ f.support) :
    Finsupp.weight w b ≤ Finsupp.weight w a := by
  by_cases hba : b = a
  · subst b
    exact le_rfl
  · apply (htail b ?_).le
    rw [mem_support_iff, coeff_sub, coeff_monomial, if_neg (Ne.symm hba), zero_sub,
      neg_ne_zero]
    exact mem_support_iff.mp hb

/-- Multiplication preserves the strict weight-tail property. The proof
keeps track of the actual coefficients and works without division. -/
lemma strict_monomial_weight_tail_mul {V : Type*} (w : V → ℕ)
    (f g : MvPolynomial V R) (a b : V →₀ ℕ)
    (hf : ∀ c ∈ (monomial a (1 : R) - f).support,
      Finsupp.weight w c < Finsupp.weight w a)
    (hg : ∀ c ∈ (monomial b (1 : R) - g).support,
      Finsupp.weight w c < Finsupp.weight w b) :
    ∀ c ∈ (monomial (a+b) (1 : R) - f*g).support,
      Finsupp.weight w c < Finsupp.weight w (a+b) := by
  have he : monomial (a+b) (1 : R) - f*g =
      monomial a 1 * (monomial b 1 - g) + (monomial a 1 - f) * g := by
    have hm : monomial (a+b) (1 : R) = monomial a 1 * monomial b 1 := by
      rw [monomial_mul, one_mul]
    rw [hm]
    ring
  intro c hc
  rw [he] at hc
  rcases Finset.mem_union.mp (support_add hc) with hc | hc
  · obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hc)
    have hu' : u = a := Finset.mem_singleton.mp (support_monomial_subset hu)
    subst u
    simpa only [map_add, add_comm] using add_lt_add_left (hg v hv) (Finsupp.weight w a)
  · obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp (support_mul _ _ hc)
    simpa only [map_add] using add_lt_add_of_lt_of_le (hf u hu)
      (weight_le_of_strict_monomial_tail w g b hg v hv)

/-- Every product in the monic power basis has strictly lower diagonal
weight away from its leading monomial. -/
theorem graphParameterProducts_weight_tails (t : R) (ht : t ≠ 0)
    (G : SimpleGraph (Fin N)) (s : ℕ) :
    ∀ f ∈ graphParameterGenerators t G ^ s, f ≠ 0 →
      ∀ a ∈ (monomial (graphLexOrder.degree f) 1 - f).support,
        Finsupp.weight graphDiagonalWeight a <
          Finsupp.weight graphDiagonalWeight (graphLexOrder.degree f) := by
  induction s with
  | zero =>
      intro f hf _ a ha
      have hf' : f = 1 := by simpa only [pow_zero, Set.mem_one] using hf
      simpa [hf', ← MvPolynomial.one_def] using ha
  | succ s ih =>
      intro f hf hf0
      rw [pow_succ] at hf
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hf
      have ha0 : a ≠ 0 := fun h => hf0 (by rw [h, zero_mul])
      have hb0 : b ≠ 0 := fun h => hf0 (by rw [h, mul_zero])
      rw [MonomialOrder.degree_mul (m := graphLexOrder) ha0 hb0]
      exact strict_monomial_weight_tail_mul graphDiagonalWeight a b
        (graphLexOrder.degree a) (graphLexOrder.degree b)
        (ih a ha ha0) (graphParameterGenerators_weight_tails t ht G b hb hb0)

theorem graphParameterProducts_subset (t : R) (G : SimpleGraph (Fin N)) (s : ℕ) :
    graphParameterGenerators t G ^ s ⊆ (graphParameterIdeal t G ^ s : Set _) := by
  intro f hf
  have h := Ideal.subset_span hf
  rw [FourPapers.ideal_span_set_power] at h
  exact h

section Coefficients
variable {S : Type u} [CommRing S] [IsDomain S]

@[simp] lemma graphParameterBinomial_map (φ : R →+* S) (t : R) (i j : Fin N) :
    MvPolynomial.map φ (graphParameterBinomial t i j) = graphParameterBinomial (φ t) i j := by
  simp only [graphParameterBinomial, map_sub, MvPolynomial.map_monomial, map_one, map_pow]

theorem graphParameterGenerators_map (φ : R →+* S) (t : R) (G : SimpleGraph (Fin N)) :
    MvPolynomial.map φ '' graphParameterGenerators t G = graphParameterGenerators (φ t) G := by
  ext f
  constructor
  · rintro ⟨g, ⟨i, j, hij, hijG, rfl⟩, rfl⟩
    exact ⟨i, j, hij, hijG, graphParameterBinomial_map φ t i j⟩
  · rintro ⟨i, j, hij, hijG, rfl⟩
    exact ⟨graphParameterBinomial t i j, graphParameterBinomial_mem t hij hijG,
      graphParameterBinomial_map φ t i j⟩

theorem graphParameterIdeal_map (φ : R →+* S) (t : R) (G : SimpleGraph (Fin N)) :
    (graphParameterIdeal t G).map (MvPolynomial.map φ) = graphParameterIdeal (φ t) G := by
  rw [graphParameterIdeal, Ideal.map_span, graphParameterGenerators_map, graphParameterIdeal]

end Coefficients

section Field
variable {K : Type u} [Field K]

theorem closedGraph_parameter_power_initial_field (t : K) (ht : t ≠ 0)
    {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G) (s : ℕ) :
    FourPapers.initialIdeal graphLexOrder (graphParameterIdeal t G ^ s) =
      (finiteSublatticeIdeal (GraphRows N) (k := K) (graphEdgeLattice G)) ^ s :=
  finite_initialIdeal_power_eq (GraphRows N) graphLexOrder (graphParameterIdeal t G)
    (graphEdgeLattice G) (graphEdgeLattice_closed hG)
    (graphParameter_initialIdeal t ht (intervalLabeling_closed_for_parameter_powers hG)) s

theorem closedGraph_parameter_power_groebner_field (t : K) (ht : t ≠ 0)
    {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G) (s : ℕ) :
    graphLexOrder.IsGroebnerBasis (graphParameterGenerators t G ^ s)
      (graphParameterIdeal t G ^ s) := by
  apply FourPapers.products_isGroebnerBasis_of_initial_power graphLexOrder _ _
    (closedGraph_parameter_groebner t ht (intervalLabeling_closed_for_parameter_powers hG)) s
  rw [closedGraph_parameter_power_initial_field t ht hG s,
    graphParameter_initialIdeal t ht (intervalLabeling_closed_for_parameter_powers hG)]

end Field

/-- All products of `s` displayed quadratics form a monic Gröbner basis
of the literal `s`-th ideal power over the original coefficient domain. -/
theorem closedGraph_parameter_power_groebner (t : R) (ht : t ≠ 0)
    {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G) (s : ℕ) :
    graphLexOrder.IsGroebnerBasis (graphParameterGenerators t G ^ s)
      (graphParameterIdeal t G ^ s) := by
  let K := FractionRing R
  let φ : R →+* K := algebraMap R K
  have hφ : Function.Injective φ := IsFractionRing.injective R K
  have ht' : φ t ≠ 0 := fun h => ht (hφ (h.trans (map_zero φ).symm))
  apply (graphLexOrder.isGroebnerBasis_map_iff (φ := φ) hφ
    (graphParameterProducts_unit_leading t ht G s) (graphParameterProducts_subset t G s)).mp
  rw [Set.image_pow, graphParameterGenerators_map, Ideal.map_pow, graphParameterIdeal_map]
  exact closedGraph_parameter_power_groebner_field (φ t) ht' hG s

theorem closedGraph_integral_parameter_power_groebner {G : SimpleGraph (Fin N)}
    (hG : IntervalLabeling G) (s : ℕ) :
    graphLexOrder.IsGroebnerBasis
      (graphParameterGenerators (Polynomial.X : Polynomial ℤ) G ^ s)
      (graphParameterIdeal (Polynomial.X : Polynomial ℤ) G ^ s) :=
  closedGraph_parameter_power_groebner _ Polynomial.X_ne_zero hG s

/-- The power equality holds over the original domain, with exactly the
same coefficient ring on both sides. -/
theorem closedGraph_parameter_power_initial (t : R) (ht : t ≠ 0)
    {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G) (s : ℕ) :
    FourPapers.initialIdeal graphLexOrder (graphParameterIdeal t G ^ s) =
      (finiteSublatticeIdeal (GraphRows N) (k := R) (graphEdgeLattice G)) ^ s := by
  rw [FourPapers.initialIdeal,
    (closedGraph_parameter_power_groebner t ht hG s).span_leadingTerm_image]
  change Ideal.span ((FourPapers.leadingTermMonoidHom graphLexOrder) ''
    (graphParameterGenerators t G ^ s)) = _
  rw [Set.image_pow, FourPapers.ideal_span_set_power]
  change (Ideal.span (graphLexOrder.leadingTerm '' graphParameterGenerators t G)) ^ s = _
  rw [← (closedGraph_parameter_groebner t ht (intervalLabeling_closed_for_parameter_powers hG)).span_leadingTerm_image]
  change (FourPapers.initialIdeal graphLexOrder (graphParameterIdeal t G)) ^ s = _
  rw [graphParameter_initialIdeal t ht (intervalLabeling_closed_for_parameter_powers hG)]

/-- Standard monomials of the parameter power are precisely those outside
the literal monomial power. This is an equality of the actual basis index
sets, not a comparison of their cardinalities. -/
theorem graphParameterPower_standardMonomials (t : R) (ht : t ≠ 0)
    {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G) (s : ℕ)
    (a : Exponent (FiniteVariable (GraphRows N))) :
    a ∈ graphLexOrder.standardMonomials (graphParameterIdeal t G ^ s) ↔
      ¬ Contains (exponentPowerFamily (finiteRowFamily (GraphRows N) (graphEdgeLattice G)) s) a := by
  have h := monomial_mem_initial_iff_not_standard graphLexOrder
    (graphParameterIdeal t G ^ s) (graphParameterGenerators t G ^ s)
    (closedGraph_parameter_power_groebner t ht hG s)
    (graphParameterProducts_unit_leading t ht G s) a
  change monomial a (1 : R) ∈
      FourPapers.initialIdeal graphLexOrder (graphParameterIdeal t G ^ s) ↔ _ at h
  rw [closedGraph_parameter_power_initial t ht hG s, ← finitePowerFamily_ideal,
    monomial_mem_iff] at h
  simpa only [not_not] using (not_congr h).symm

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- The actual degree-`q` submodule of `J(t)^s` and the actual degree-`q`
image in its quotient are finite free over `R`. In the integral family
this is freeness over `ℤ[z]`, before any specialization. -/
theorem closedGraph_parameter_power_pieces_finite_free (t : R) (ht : t ≠ 0)
    {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G) (s q : ℕ) :
    (Module.Free R (idealWeightedComponent (graphParameterIdeal t G ^ s)
        (fun _ => (1 : ℕ)) q) ∧
      Module.Finite R (idealWeightedComponent (graphParameterIdeal t G ^ s)
        (fun _ => (1 : ℕ)) q)) ∧
    (Module.Free R (quotientWeightedComponent (graphParameterIdeal t G ^ s)
        (fun _ => (1 : ℕ)) q) ∧
      Module.Finite R (quotientWeightedComponent (graphParameterIdeal t G ^ s)
        (fun _ => (1 : ℕ)) q)) :=
  groebnerWeightedPieces_finite_free graphLexOrder (graphParameterIdeal t G ^ s)
    (graphParameterGenerators t G ^ s) (closedGraph_parameter_power_groebner t ht hG s)
    (graphParameterProducts_unit_leading t ht G s) (fun _ => 1)
    (fun _ => one_ne_zero) (graphParameterPower_ordinary_homogeneous t G s) q

end FourPapers.Sublattice

end
end
end


end
