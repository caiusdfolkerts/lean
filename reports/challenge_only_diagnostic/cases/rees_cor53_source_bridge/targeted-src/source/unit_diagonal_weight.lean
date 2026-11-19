module
public import shared_results.part018
public import unit_interval_power_foundation
public import Mathlib.Algebra.Order.Rearrangement

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.FacetDiagonalWeight -/
section

/-!
# A concrete natural diagonal weight for every maximal-minor power

The variable in row `r`, column `j` has weight `r*j`. Strict rearrangement
makes the diagonal the unique largest-weight term of every increasing
minor. Multiplication preserves the strict-tail property. Thus the
numerical filtration used for Theorem 6.5 is supplied explicitly for all
of the actual product Gröbner generators, without assuming a weight
realization theorem for arbitrary monomial orders.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice
open Classical MvPolynomial CommAlg.Polymatroid
open scoped Pointwise
universe u
variable {d N : ℕ}

def facetDiagonalWeight (v : FiniteVariable.{u} (UnitIntervalRows d N)) : ℕ :=
  v.1.val * v.2.down.val

lemma facetMinorTermExponent_weight (a : (Fin (d+1) → Fin N))
    (σ : Equiv.Perm (Fin (d+1))) :
    Finsupp.weight facetDiagonalWeight (facetMinorTermExponent a σ) =
      ∑ i, (σ i).val * (a i).val := by
  simp only [facetMinorTermExponent, map_sum, Finsupp.weight_single,
    one_nsmul, facetDiagonalWeight]

/-- Strict rearrangement over the natural numbers gives a concrete
weight inequality for every off-diagonal determinant term. -/
lemma facetMinorTermExponent_weight_lt_diagonal
    (a : (Fin (d+1) → Fin N)) (ha : StrictMono a)
    (σ : Equiv.Perm (Fin (d+1))) (hσ : σ ≠ 1) :
    Finsupp.weight facetDiagonalWeight (facetMinorTermExponent a σ) <
      Finsupp.weight facetDiagonalWeight (finiteRowExponent (UnitIntervalRows d N) a) := by
  rw [← facetMinorTermExponent_one a, facetMinorTermExponent_weight,
    facetMinorTermExponent_weight]
  simp only [Equiv.Perm.one_apply]
  have hmono : Monovary (fun i : Fin (d+1) => i.val) (fun i => (a i).val) := by
    intro i j hij
    exact (ha.lt_iff_lt.mp hij).le
  apply hmono.sum_comp_perm_mul_lt_sum_mul_iff.mpr
  intro hcross
  obtain ⟨r, hprev, hr⟩ := permutation_first_moved σ hσ
  have hinv : r < σ.symm r := by
    by_contra h
    rcases (le_of_not_gt h).eq_or_lt with he | he
    · have hfix := σ.apply_symm_apply r
      rw [he] at hfix
      exact hr.ne hfix.symm
    · have hfix := hprev (σ.symm r) he
      rw [σ.apply_symm_apply] at hfix
      exact he.ne hfix.symm
  have hle : (σ r).val ≤ r.val := by
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hcross (ha hinv)
  have hlt : r.val < (σ r).val := hr
  exact (not_le_of_gt hlt) hle

section Ring
variable {k : Type u} [CommRing k] [Nontrivial k]

theorem facetMinor_weight_tail (a : (Fin (d+1) → Fin N))
    (ha : StrictMono a) (b : Exponent (FiniteVariable.{u} (UnitIntervalRows d N)))
    (hb : b ∈ (monomial (facetLexOrder.degree (facetMinor (k := k) a)) (1 : k) -
      facetMinor (k := k) a).support) :
    Finsupp.weight facetDiagonalWeight b <
      Finsupp.weight facetDiagonalWeight (facetLexOrder.degree (facetMinor (k := k) a)) := by
  rw [facetMinor_degree a ha] at hb ⊢
  have hbd : b ≠ finiteRowExponent (UnitIntervalRows d N) a := by
    intro he
    rw [he, mem_support_iff, coeff_sub, coeff_monomial, if_pos rfl,
      facetMinor_diagonal_coefficient a ha, sub_self] at hb
    exact hb rfl
  have hc : (facetMinor (k := k) a).coeff b ≠ 0 := by
    have h := mem_support_iff.mp hb
    rw [coeff_sub, coeff_monomial, if_neg (Ne.symm hbd), zero_sub, neg_ne_zero] at h
    exact h
  rw [facetMinor_expansion, coeff_sum] at hc
  obtain ⟨σ, _, hσc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  have he : facetMinorTermExponent a σ = b := by
    by_contra hn
    simp only [coeff_monomial, if_neg hn] at hσc
    exact hσc rfl
  have hσ : σ ≠ 1 := by
    intro h
    rw [h, facetMinorTermExponent_one] at he
    exact hbd he.symm
  rw [← he]
  exact facetMinorTermExponent_weight_lt_diagonal a ha σ hσ

theorem unitInterval_minorGenerators_weight_tails
    {E : Finset ((Fin (d+1) → Fin N))} (hE : UnitIntervalFacetFamily E) :
    ∀ f ∈ facetMinorGenerators (k := k) E, f ≠ 0 →
      ∀ b ∈ (monomial (facetLexOrder.degree f) 1 - f).support,
        Finsupp.weight facetDiagonalWeight b <
          Finsupp.weight facetDiagonalWeight (facetLexOrder.degree f) := by
  rintro f ⟨a, ha, rfl⟩ _ b hb
  exact facetMinor_weight_tail a (hE.increasing a ha) b hb

end Ring

section Domain
variable {k : Type u} [CommRing k] [IsDomain k]

theorem unitInterval_minorProducts_weight_tails
    {E : Finset ((Fin (d+1) → Fin N))} (hE : UnitIntervalFacetFamily E)
    (s : ℕ) :
    ∀ f ∈ facetMinorGenerators (k := k) E ^ s, f ≠ 0 →
      ∀ b ∈ (monomial (facetLexOrder.degree f) 1 - f).support,
        Finsupp.weight facetDiagonalWeight b <
          Finsupp.weight facetDiagonalWeight (facetLexOrder.degree f) := by
  induction s with
  | zero =>
      intro f hf _ b hb
      have hf' : f = 1 := by simpa only [pow_zero, Set.mem_one] using hf
      simpa [hf', ← MvPolynomial.one_def] using hb
  | succ s ih =>
      intro f hf hf0
      rw [pow_succ] at hf
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hf
      have ha0 : a ≠ 0 := fun h => hf0 (by rw [h, zero_mul])
      have hb0 : b ≠ 0 := fun h => hf0 (by rw [h, mul_zero])
      rw [MonomialOrder.degree_mul (m := facetLexOrder) ha0 hb0]
      exact strict_monomial_weight_tail_mul facetDiagonalWeight a b
        (facetLexOrder.degree a) (facetLexOrder.degree b)
        (ih a ha ha0) (unitInterval_minorGenerators_weight_tails hE b hb hb0)

/-- A uniform finite bound for the actual ordinary-degree filtration. -/
theorem facetDiagonalWeight_le (v : FiniteVariable.{u} (UnitIntervalRows d N)) :
    facetDiagonalWeight v ≤ d * N :=
  Nat.mul_le_mul (Nat.le_of_lt_succ v.1.isLt) v.2.down.isLt.le

end Domain
end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.unitInterval_minorProducts_weight_tails

end
end


end
