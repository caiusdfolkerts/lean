module
public import paper_results.monomial_presentation

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency true

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ReesStandard -/
section

set_option autoImplicit false

/-!
# Leading terms and standardness for the Rees presentation
-/

noncomputable section

namespace FourPapers.Sublattice

open Classical MvPolynomial Finset
open scoped MonomialOrder

variable {R k : Type*} [Fintype R] [LinearOrder R] [CommRing k] [Nontrivial k]
variable {E : Finset (R → ℕ)}

def ReesRelations (hE : LatticeClosed E) : Set (MvPolynomial (ReesVariable E) k) :=
  {f | ∃ a b : E, ¬ a.val ≤ b.val ∧ ¬ b.val ≤ a.val ∧ f = sortingRelation hE a b} ∪
  {f | ∃ b a : E, b.val ≤ a.val ∧ b.val ≠ a.val ∧ f = coefficientRelation b a}

lemma reesRelations_vanish (hE : LatticeClosed E) :
    ∀ f ∈ ReesRelations (k := k) hE, reesPresentationMap E f = 0 := by
  intro f hf
  rcases hf with ⟨a,b,hab,hba,rfl⟩ | ⟨b,a,hba,hne,rfl⟩ <;> simp

lemma degree_sortingRelation (hE : LatticeClosed E)
    (m : MonomialOrder (ReesVariable E)) (a b : E)
    (hab : ¬ a.val ≤ b.val) (hba : ¬ b.val ≤ a.val) :
    (weightedOrder m (presentationWeight E)).degree (sortingRelation (k := k) hE a b) =
      sortingHeadExponent a b := by
  have h := sorting_weight_order hE m a b hab hba
  have hd : (weightedOrder m (presentationWeight E)).degree
      (monomial (sortingTailExponent hE a b) (1 : k))
      ≺[weightedOrder m (presentationWeight E)]
      (weightedOrder m (presentationWeight E)).degree
        (monomial (sortingHeadExponent a b) (1 : k)) := by
    simpa only [MonomialOrder.degree_monomial,one_ne_zero,ite_false] using h
  simpa only [sortingRelation,MonomialOrder.degree_monomial,one_ne_zero,ite_false] using
    (weightedOrder m (presentationWeight E)).degree_sub_of_lt hd

lemma monic_sortingRelation (hE : LatticeClosed E)
    (m : MonomialOrder (ReesVariable E)) (a b : E)
    (hab : ¬ a.val ≤ b.val) (hba : ¬ b.val ≤ a.val) :
    (weightedOrder m (presentationWeight E)).Monic (sortingRelation (k := k) hE a b) := by
  have h := sorting_weight_order hE m a b hab hba
  have hd : (weightedOrder m (presentationWeight E)).degree
      (monomial (sortingTailExponent hE a b) (1 : k))
      ≺[weightedOrder m (presentationWeight E)]
      (weightedOrder m (presentationWeight E)).degree
        (monomial (sortingHeadExponent a b) (1 : k)) := by
    simpa only [MonomialOrder.degree_monomial,one_ne_zero,ite_false] using h
  simpa only [MonomialOrder.Monic,sortingRelation,MonomialOrder.leadingCoeff_monomial] using
    (weightedOrder m (presentationWeight E)).leadingCoeff_sub_of_lt hd

lemma degree_coefficientRelation (m : MonomialOrder (ReesVariable E)) (b a : E)
    (hba : b.val ≤ a.val) (hne : b.val ≠ a.val) :
    (weightedOrder m (presentationWeight E)).degree (coefficientRelation (k := k) b a) =
      coefficientHeadExponent b a := by
  have h := coefficient_weight_order m b a hba hne
  have hd : (weightedOrder m (presentationWeight E)).degree
      (monomial (coefficientHeadExponent a b) (1 : k))
      ≺[weightedOrder m (presentationWeight E)]
      (weightedOrder m (presentationWeight E)).degree
        (monomial (coefficientHeadExponent b a) (1 : k)) := by
    simpa only [MonomialOrder.degree_monomial,one_ne_zero,ite_false] using h
  simpa only [coefficientRelation,MonomialOrder.degree_monomial,one_ne_zero,ite_false] using
    (weightedOrder m (presentationWeight E)).degree_sub_of_lt hd

lemma monic_coefficientRelation (m : MonomialOrder (ReesVariable E)) (b a : E)
    (hba : b.val ≤ a.val) (hne : b.val ≠ a.val) :
    (weightedOrder m (presentationWeight E)).Monic (coefficientRelation (k := k) b a) := by
  have h := coefficient_weight_order m b a hba hne
  have hd : (weightedOrder m (presentationWeight E)).degree
      (monomial (coefficientHeadExponent a b) (1 : k))
      ≺[weightedOrder m (presentationWeight E)]
      (weightedOrder m (presentationWeight E)).degree
        (monomial (coefficientHeadExponent b a) (1 : k)) := by
    simpa only [MonomialOrder.degree_monomial,one_ne_zero,ite_false] using h
  simpa only [MonomialOrder.Monic,coefficientRelation,MonomialOrder.leadingCoeff_monomial] using
    (weightedOrder m (presentationWeight E)).leadingCoeff_sub_of_lt hd

lemma reesRelations_monic (hE : LatticeClosed E) (m : MonomialOrder (ReesVariable E)) :
    ∀ f ∈ ReesRelations (k := k) hE,
      (weightedOrder m (presentationWeight E)).Monic f := by
  intro f hf
  rcases hf with ⟨a,b,hab,hba,rfl⟩ | ⟨b,a,hba,hne,rfl⟩
  · exact monic_sortingRelation hE m a b hab hba
  · exact monic_coefficientRelation m b a hba hne

/-- Standardness in the actual polynomial presentation is exactly the chain and
coefficient condition used in the normal-form proof. -/
theorem relationStandard_iff (hE : LatticeClosed E)
    (m : MonomialOrder (ReesVariable E)) (c : ReesVariable E →₀ ℕ) :
    c ∈ RelationStandard (weightedOrder m (presentationWeight E)) (ReesRelations (k := k) hE) ↔
      StandardExponent E (factorPart c) (coefficientPart c) := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · intro a b ha hb
      by_contra hn
      push_neg at hn
      have hmem : sortingRelation (k := k) hE a b ∈ ReesRelations hE :=
        Or.inl ⟨a,b,hn.1,hn.2,rfl⟩
      have hnon := (monic_sortingRelation (k := k) hE m a b hn.1 hn.2).ne_zero
      have havoid := h _ hmem hnon
      rw [degree_sortingRelation hE m a b hn.1 hn.2] at havoid
      apply havoid
      exact (sortingHeadExponent_le_iff (fun (he : a = b) => hn.1 (by simpa only [he] using (le_refl b.val))) c).mpr ⟨ha,hb⟩
    · intro a ha b hb hba hne hv
      let b' : E := ⟨b,hb⟩
      have hmem : coefficientRelation (k := k) b' a ∈ ReesRelations hE :=
        Or.inr ⟨b',a,hba,hne,rfl⟩
      have hnon := (monic_coefficientRelation (k := k) m b' a hba hne).ne_zero
      have havoid := h _ hmem hnon
      rw [degree_coefficientRelation m b' a hba hne] at havoid
      exact havoid ((coefficientHeadExponent_le_iff hba c).mpr ⟨ha,hv⟩)
  · intro h g hg _
    rcases hg with ⟨a,b,hab,hba,rfl⟩ | ⟨b,a,hba,hne,rfl⟩
    · rw [degree_sortingRelation hE m a b hab hba]
      intro hdiv
      have hp := (sortingHeadExponent_le_iff (fun (he : a = b) => hab (by simpa only [he] using (le_refl b.val))) c).mp hdiv
      exact (h.1 a b hp.1 hp.2).elim hab hba
    · rw [degree_coefficientRelation m b a hba hne]
      intro hdiv
      have hp := (coefficientHeadExponent_le_iff hba c).mp hdiv
      exact h.2 a hp.1 b.val b.property hba hne hp.2

end FourPapers.Sublattice

end
end

#print axioms FourPapers.Sublattice.degree_sortingRelation
#print axioms FourPapers.Sublattice.monic_sortingRelation
#print axioms FourPapers.Sublattice.degree_coefficientRelation
#print axioms FourPapers.Sublattice.monic_coefficientRelation
#print axioms FourPapers.Sublattice.reesRelations_monic
#print axioms FourPapers.Sublattice.relationStandard_iff

end
