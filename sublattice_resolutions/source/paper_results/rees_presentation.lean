module
public import paper_results.rees_standard

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency true

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ReesPresentation -/
section

set_option autoImplicit false

/-!
# The complete polynomial presentation

The final normal-form argument is an application of division to the actual
polynomial kernel. Linear independence is inherited from distinct monomials in
`S[t]`; it is not imposed as an extra hypothesis on the sublattice.
-/

noncomputable section

namespace FourPapers.Sublattice

open Classical MvPolynomial Finset

variable {R k : Type*} [Fintype R] [LinearOrder R] [CommRing k] [Nontrivial k]
variable {E : Finset (R → ℕ)}

/-- Injectivity on all actual standard exponent vectors in the presentation. -/
theorem reesExponentMap_injective_standard (hE : LatticeClosed E)
    (m : MonomialOrder (ReesVariable E)) :
    Function.Injective (fun c : RelationStandard
      (weightedOrder m (presentationWeight E)) (ReesRelations (k := k) hE) =>
        reesExponentMap E c.val) := by
  intro c d h
  have hc := (relationStandard_iff hE m c.val).mp c.property
  have hd := (relationStandard_iff hE m d.val).mp d.property
  have hdeg : (factorPart c.val).toMultiset.card = (factorPart d.val).toMultiset.card := by
    simpa only [reesExponentMap_none] using congrArg (fun e => e none) h
  have him : standardImageExponent (factorPart c.val) (coefficientPart c.val) =
      standardImageExponent (factorPart d.val) (coefficientPart d.val) := by
    funext x
    simpa only [reesExponentMap_some] using congrArg (fun e => e (some x)) h
  obtain ⟨ht,hv⟩ := standardExponent_image_injective hE.1 hc hd hdeg him
  apply Subtype.ext
  apply exponent_eq_of_parts
  · exact DFunLike.coe_injective hv
  · exact ht

lemma rees_standard_images_independent (hE : LatticeClosed E)
    (m : MonomialOrder (ReesVariable E)) :
    LinearIndependent k (fun c : RelationStandard
      (weightedOrder m (presentationWeight E)) (ReesRelations (k := k) hE) =>
        reesPresentationMap E (monomial c.val (1 : k))) := by
  have hh := (MvPolynomial.basisMonomials (Option (R × ℕ)) k).linearIndependent.comp
    (fun c : RelationStandard (weightedOrder m (presentationWeight E))
      (ReesRelations (k := k) hE) => reesExponentMap E c.val)
    (reesExponentMap_injective_standard hE m)
  simpa only [Function.comp_def,MvPolynomial.coe_basisMonomials,
    reesPresentationMap_monomial] using hh

/-- Proposition 2.2, in the actual polynomial presentation and over every
nontrivial commutative coefficient ring. -/
theorem sublattice_rees_groebnerBasis (hE : LatticeClosed E)
    (m : MonomialOrder (ReesVariable E)) :
    (weightedOrder m (presentationWeight E)).IsGroebnerBasis
      (ReesRelations (k := k) hE) (RingHom.ker (reesPresentationMap E).toRingHom) := by
  apply isGroebnerBasis_kernel_of_independent
  · exact reesRelations_vanish hE
  · intro g hg _
    rw [(reesRelations_monic hE m g hg)]
    exact isUnit_one
  · exact rees_standard_images_independent hE m

/-- The sorting and coefficient relations generate exactly the polynomial kernel. -/
theorem sublattice_rees_kernel (hE : LatticeClosed E)
    (m : MonomialOrder (ReesVariable E)) :
    RingHom.ker (reesPresentationMap (k := k) E).toRingHom =
      Ideal.span (ReesRelations hE) :=
  (sublattice_rees_groebnerBasis hE m).ideal_eq_span

end FourPapers.Sublattice

end
end

#print axioms FourPapers.Sublattice.reesExponentMap_injective_standard
#print axioms FourPapers.Sublattice.rees_standard_images_independent
#print axioms FourPapers.Sublattice.sublattice_rees_groebnerBasis
#print axioms FourPapers.Sublattice.sublattice_rees_kernel

end
