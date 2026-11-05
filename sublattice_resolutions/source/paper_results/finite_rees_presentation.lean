module
public import paper_results.rees_presentation
public import paper_results.part006

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency true

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.FiniteReesPresentation -/
section

/-!
# The universal Gröbner presentation in the exact finite polynomial ring

The presentation variables are precisely the finite row variables and one variable
for every element of the finite sublattice. The displayed sorting and predecessor
relations are monic, have the claimed leading monomials, and generate the kernel
of the literal finite Rees presentation map. Standard-image independence is proved
in that finite target polynomial ring, so no unused columns are adjoined.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace FourPapers.Sublattice

open Classical MvPolynomial CommAlg.Polymatroid
open scoped MonomialOrder
universe u v w
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
variable {k : Type v} [CommRing k] [Nontrivial k]

/-- The explicit positive concave weight restricted to the paper's exact variables. -/
def finiteReesPresentationWeight (E : Finset (FiniteTuple n)) : FiniteReesVariable.{u} E → ℕ :=
  fun x => presentationWeight (finiteTupleImage E) (finiteReesVariableEmbedding E x)

lemma finiteReesPresentationWeight_pos (x : FiniteReesVariable.{u} E) :
    0 < finiteReesPresentationWeight.{u} E x :=
  presentationWeight_pos _ _

/-- Any monomial order may break ties after the explicit positive weight. -/
abbrev finiteReesPresentationOrder (m : MonomialOrder.{u,w} (FiniteReesVariable.{u} E)) :
    MonomialOrder.{u,w} (FiniteReesVariable.{u} E) :=
  weightedOrder m (finiteReesPresentationWeight.{u} E)

lemma finiteSorting_weight_strict (hE : finiteLatticeClosed n E) (a b : E)
    (hab : ¬ a.val ≤ b.val) (hba : ¬ b.val ≤ a.val) :
    Finsupp.weight (finiteReesPresentationWeight.{u} E) (finiteSortingTailExponent.{u} hE a b) <
      Finsupp.weight (finiteReesPresentationWeight.{u} E) (finiteSortingHeadExponent.{u} a b) := by
  have h := sorting_weight_decreases (finiteTupleImage_closed hE)
    (finiteTupleImageEquiv E a) (finiteTupleImageEquiv E b) hab hba
  change Finsupp.weight (presentationWeight (finiteTupleImage E)) _ <
    Finsupp.weight (presentationWeight (finiteTupleImage E)) _ at h
  rw [← finiteSortingTailExponent_embedding.{u} hE a b,
    ← finiteSortingHeadExponent_embedding.{u} a b,
    presentationWeight_embDomain, presentationWeight_embDomain] at h
  exact h

lemma finiteCoefficient_weight_strict (b a : E) (hba : b.val ≤ a.val) (hne : b.val ≠ a.val) :
    Finsupp.weight (finiteReesPresentationWeight.{u} E) (finiteCoefficientHeadExponent.{u} a b) <
      Finsupp.weight (finiteReesPresentationWeight.{u} E) (finiteCoefficientHeadExponent.{u} b a) := by
  have h := coefficient_weight_decreases (finiteTupleImageEquiv E b) (finiteTupleImageEquiv E a)
    hba (fun h => hne (finiteTupleToNat_injective h))
  change Finsupp.weight (presentationWeight (finiteTupleImage E)) _ <
    Finsupp.weight (presentationWeight (finiteTupleImage E)) _ at h
  rw [← finiteCoefficientHeadExponent_embedding.{u} a b,
    ← finiteCoefficientHeadExponent_embedding.{u} b a,
    presentationWeight_embDomain, presentationWeight_embDomain] at h
  exact h

/-- No admissibility premise is added: the explicit positive weight satisfies it. -/
theorem finiteReesPresentationWeight_admissible (hE : finiteLatticeClosed n E) :
    FiniteReesWeightAdmissible hE (finiteReesPresentationWeight.{u} E) :=
  (finiteReesWeightAdmissible_iff hE _).mpr
    ⟨finiteSorting_weight_strict hE, finiteCoefficient_weight_strict⟩

def finiteSortingRelation (hE : finiteLatticeClosed n E) (a b : E) :
    MvPolynomial (FiniteReesVariable.{u} E) k :=
  monomial (finiteSortingHeadExponent.{u} a b) 1 - monomial (finiteSortingTailExponent.{u} hE a b) 1

def finiteCoefficientRelation (b a : E) : MvPolynomial (FiniteReesVariable.{u} E) k :=
  monomial (finiteCoefficientHeadExponent.{u} b a) 1 - monomial (finiteCoefficientHeadExponent.{u} a b) 1

/-- Exactly the two families of binomials displayed in Proposition 2.2. -/
def FiniteReesRelations (hE : finiteLatticeClosed n E) : Set (MvPolynomial (FiniteReesVariable.{u} E) k) :=
  {f | ∃ a b : E, ¬ a.val ≤ b.val ∧ ¬ b.val ≤ a.val ∧ f = finiteSortingRelation hE a b} ∪
  {f | ∃ b a : E, b.val ≤ a.val ∧ b.val ≠ a.val ∧ f = finiteCoefficientRelation b a}

@[simp] lemma finiteReesPresentationMap_monomial (c : FiniteReesVariable.{u} E →₀ ℕ) (a : k) :
    finiteReesPresentationMap.{u} E k (monomial c a) = monomial (finiteReesExponentMap E c) a := by
  change AddMonoidAlgebra.mapDomain (finiteReesExponentMap E) (AddMonoidAlgebra.single c a) = _
  exact AddMonoidAlgebra.mapDomain_single

lemma finiteReesRelations_vanish (hE : finiteLatticeClosed n E) :
    ∀ f ∈ FiniteReesRelations.{u} (k := k) hE, finiteReesPresentationMap.{u} E k f = 0 := by
  intro f hf
  rcases hf with ⟨a,b,hab,hba,rfl⟩ | ⟨b,a,hba,hne,rfl⟩
  · simp [finiteSortingRelation, finiteSorting_exponent_images hE a b]
  · simp [finiteCoefficientRelation, finiteCoefficient_exponent_images b a]

private theorem finitePresentation_binomial_leading
    (m : MonomialOrder.{u,w} (FiniteReesVariable.{u} E)) {c e : FiniteReesVariable.{u} E →₀ ℕ}
    (h : Finsupp.weight (finiteReesPresentationWeight.{u} E) e <
      Finsupp.weight (finiteReesPresentationWeight.{u} E) c) :
    (finiteReesPresentationOrder m).degree (monomial c (1 : k) - monomial e 1) = c ∧
      (finiteReesPresentationOrder m).Monic (monomial c (1 : k) - monomial e 1) := by
  have hlt := weightedOrder_lt_of_weight_lt m (finiteReesPresentationWeight.{u} E) h
  have hd : (finiteReesPresentationOrder m).degree (monomial e (1 : k))
      ≺[finiteReesPresentationOrder m]
        (finiteReesPresentationOrder m).degree (monomial c (1 : k)) := by
    simpa only [finiteReesPresentationOrder, MonomialOrder.degree_monomial, one_ne_zero, ite_false] using hlt
  constructor
  · simpa only [MonomialOrder.degree_monomial, one_ne_zero, ite_false] using
      (finiteReesPresentationOrder m).degree_sub_of_lt hd
  · simpa only [MonomialOrder.Monic, MonomialOrder.leadingCoeff_monomial] using
      (finiteReesPresentationOrder m).leadingCoeff_sub_of_lt hd

theorem finiteSortingRelation_leading (hE : finiteLatticeClosed n E)
    (m : MonomialOrder.{u,w} (FiniteReesVariable.{u} E)) (a b : E)
    (hab : ¬ a.val ≤ b.val) (hba : ¬ b.val ≤ a.val) :
    (finiteReesPresentationOrder m).degree (finiteSortingRelation (k := k) hE a b) =
      finiteSortingHeadExponent.{u} a b ∧
    (finiteReesPresentationOrder m).Monic (finiteSortingRelation (k := k) hE a b) :=
  finitePresentation_binomial_leading m (finiteSorting_weight_strict hE a b hab hba)

theorem finiteCoefficientRelation_leading (m : MonomialOrder.{u,w} (FiniteReesVariable.{u} E))
    (b a : E) (hba : b.val ≤ a.val) (hne : b.val ≠ a.val) :
    (finiteReesPresentationOrder m).degree (finiteCoefficientRelation (k := k) b a) =
      finiteCoefficientHeadExponent.{u} b a ∧
    (finiteReesPresentationOrder m).Monic (finiteCoefficientRelation (k := k) b a) :=
  finitePresentation_binomial_leading m (finiteCoefficient_weight_strict b a hba hne)

lemma finiteReesRelations_monic (hE : finiteLatticeClosed n E)
    (m : MonomialOrder.{u,w} (FiniteReesVariable.{u} E)) :
    ∀ f ∈ FiniteReesRelations.{u} (k := k) hE, (finiteReesPresentationOrder m).Monic f := by
  intro f hf
  rcases hf with ⟨a,b,hab,hba,rfl⟩ | ⟨b,a,hba,hne,rfl⟩
  · exact (finiteSortingRelation_leading hE m a b hab hba).2
  · exact (finiteCoefficientRelation_leading m b a hba hne).2

lemma finiteReesRelations_degrees (hE : finiteLatticeClosed n E)
    (m : MonomialOrder.{u,w} (FiniteReesVariable.{u} E)) :
    (finiteReesPresentationOrder m).degree '' FiniteReesRelations.{u} (k := k) hE =
      finiteReesInitialHeads E := by
  ext c
  constructor
  · rintro ⟨f,hf,rfl⟩
    rcases hf with ⟨a,b,hab,hba,rfl⟩ | ⟨b,a,hba,hne,rfl⟩
    · exact Or.inl ⟨a,b,hab,hba,(finiteSortingRelation_leading hE m a b hab hba).1⟩
    · exact Or.inr ⟨b,a,hba,hne,(finiteCoefficientRelation_leading m b a hba hne).1⟩
  · rintro (⟨a,b,hab,hba,rfl⟩ | ⟨b,a,hba,hne,rfl⟩)
    · exact ⟨finiteSortingRelation hE a b,Or.inl ⟨a,b,hab,hba,rfl⟩,
        (finiteSortingRelation_leading hE m a b hab hba).1⟩
    · exact ⟨finiteCoefficientRelation b a,Or.inr ⟨b,a,hba,hne,rfl⟩,
        (finiteCoefficientRelation_leading m b a hba hne).1⟩

/-- Standardness is identified with the actual finite chain/colon condition. -/
theorem finiteRelationStandard_iff (hE : finiteLatticeClosed n E)
    (m : MonomialOrder.{u,w} (FiniteReesVariable.{u} E)) (c : FiniteReesVariable.{u} E →₀ ℕ) :
    c ∈ RelationStandard (finiteReesPresentationOrder m) (FiniteReesRelations.{u} (k := k) hE) ↔
      FiniteReesStandard c := by
  rw [finiteReesStandard_iff_noInitialHead]
  constructor
  · intro h ⟨a,ha,hac⟩
    rw [← finiteReesRelations_degrees (k := k) hE m] at ha
    obtain ⟨f,hf,rfl⟩ := ha
    exact h f hf ((finiteReesRelations_monic hE m f hf).ne_zero) hac
  · intro h f hf hne hfc
    apply h
    refine ⟨_, ?_, hfc⟩
    rw [← finiteReesRelations_degrees (k := k) hE m]
    exact ⟨f,hf,rfl⟩

lemma finiteRees_standard_images_independent (hE : finiteLatticeClosed n E)
    (m : MonomialOrder.{u,w} (FiniteReesVariable.{u} E)) :
    LinearIndependent k (fun c : RelationStandard
      (finiteReesPresentationOrder m) (FiniteReesRelations.{u} (k := k) hE) =>
        finiteReesPresentationMap.{u} E k (monomial c.val 1)) := by
  have hinj : Function.Injective (fun c : RelationStandard
      (finiteReesPresentationOrder m) (FiniteReesRelations.{u} (k := k) hE) =>
        finiteReesExponentMap E c.val) := by
    intro c e he
    apply Subtype.ext
    exact finiteReesStandard_image_injective hE
      ((finiteRelationStandard_iff hE m c.val).mp c.property)
      ((finiteRelationStandard_iff hE m e.val).mp e.property) he
  have h := (MvPolynomial.basisMonomials (Option (FiniteVariable.{u} n)) k).linearIndependent.comp
    (fun c : RelationStandard (finiteReesPresentationOrder m) (FiniteReesRelations.{u} (k := k) hE) =>
      finiteReesExponentMap E c.val) hinj
  simpa only [Function.comp_def, MvPolynomial.coe_basisMonomials,
    finiteReesPresentationMap_monomial] using h

/-- Proposition 2.2 in the literal finite polynomial presentation. Its only
mathematical premise is that the finite tuple family is a sublattice. -/
theorem finite_sublattice_rees_groebnerBasis (hE : finiteLatticeClosed n E)
    (m : MonomialOrder.{u,w} (FiniteReesVariable.{u} E)) :
    (finiteReesPresentationOrder m).IsGroebnerBasis (FiniteReesRelations.{u} (k := k) hE)
      (RingHom.ker (finiteReesPresentationMap.{u} E k).toRingHom) := by
  apply isGroebnerBasis_kernel_of_independent
  · exact finiteReesRelations_vanish hE
  · intro f hf _
    rw [finiteReesRelations_monic hE m f hf]
    exact isUnit_one
  · exact finiteRees_standard_images_independent hE m

/-- The exact finite sorting and coefficient relations generate the entire kernel. -/
theorem finite_sublattice_rees_kernel (hE : finiteLatticeClosed n E)
    (m : MonomialOrder.{u,w} (FiniteReesVariable.{u} E)) :
    RingHom.ker (finiteReesPresentationMap.{u} E k).toRingHom =
      Ideal.span (FiniteReesRelations.{u} (k := k) hE) :=
  (finite_sublattice_rees_groebnerBasis (k := k) hE m).ideal_eq_span

/-- The actual initial ideal is exactly the displayed sorting/predecessor monomial ideal. -/
theorem finite_sublattice_rees_initialIdeal (hE : finiteLatticeClosed n E)
    (m : MonomialOrder.{u,w} (FiniteReesVariable.{u} E)) :
    Ideal.span ((finiteReesPresentationOrder m).leadingTerm ''
      (RingHom.ker (finiteReesPresentationMap.{u} E k).toRingHom : Set _)) =
        finiteReesInitialIdeal k E := by
  rw [(finite_sublattice_rees_groebnerBasis (k := k) hE m).span_leadingTerm_image]
  unfold finiteReesInitialIdeal
  congr 1
  rw [← finiteReesRelations_degrees (k := k) hE m, Set.image_image]
  apply Set.image_congr
  intro f hf
  exact congrArg (monomial ((finiteReesPresentationOrder m).degree f))
    (finiteReesRelations_monic hE m f hf)

/-- All displayed relations preserve the literal fine exponent together with Rees degree. -/
theorem finiteReesRelations_homogeneous (hE : finiteLatticeClosed n E) :
    ∀ f ∈ FiniteReesRelations.{u} (k := k) hE,
      ∃ α, f.IsWeightedHomogeneous (finiteReesVariableExponent E) α := by
  intro f hf
  rcases hf with ⟨a,b,hab,hba,rfl⟩ | ⟨b,a,hba,hne,rfl⟩
  · refine ⟨finiteReesExponentMap E (finiteSortingHeadExponent.{u} a b), ?_⟩
    exact (isWeightedHomogeneous_monomial _ _ (1 : k) rfl).sub
      (isWeightedHomogeneous_monomial _ _ (1 : k) (finiteSorting_exponent_images hE a b).symm)
  · refine ⟨finiteReesExponentMap E (finiteCoefficientHeadExponent.{u} b a), ?_⟩
    exact (isWeightedHomogeneous_monomial _ _ (1 : k) rfl).sub
      (isWeightedHomogeneous_monomial _ _ (1 : k) (finiteCoefficient_exponent_images b a).symm)


/-- An order exists with exactly the monic Gröbner presentation of Proposition 2.2.
The order is constructed from the finite variable set; it is not a hypothesis. -/
theorem proposition22 (hE : finiteLatticeClosed n E) :
    ∃ m : MonomialOrder.{u,u} (FiniteReesVariable.{u} E),
      m.IsGroebnerBasis (FiniteReesRelations.{u} (k := k) hE)
        (RingHom.ker (finiteReesPresentationMap.{u} E k).toRingHom) ∧
      (∀ f ∈ FiniteReesRelations.{u} (k := k) hE, m.Monic f) ∧
      RingHom.ker (finiteReesPresentationMap.{u} E k).toRingHom =
        Ideal.span (FiniteReesRelations.{u} (k := k) hE) ∧
      Ideal.span (m.leadingTerm ''
        (RingHom.ker (finiteReesPresentationMap.{u} E k).toRingHom : Set _)) =
          finiteReesInitialIdeal k E := by
  let ord : LinearOrder (FiniteReesVariable.{u} E) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  let wf : @WellFoundedGT (FiniteReesVariable.{u} E) ord.toLT :=
    @Finite.to_wellFoundedGT (FiniteReesVariable.{u} E) inferInstance ord.toPreorder
  let m : MonomialOrder.{u,u} (FiniteReesVariable.{u} E) := @MonomialOrder.lex _ ord wf
  exact ⟨finiteReesPresentationOrder m,
    finite_sublattice_rees_groebnerBasis (k := k) hE m,
    finiteReesRelations_monic (k := k) hE m,
    finite_sublattice_rees_kernel (k := k) hE m,
    finite_sublattice_rees_initialIdeal (k := k) hE m⟩

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.finiteReesPresentationWeight_admissible
#print axioms FourPapers.Sublattice.finiteSortingRelation_leading
#print axioms FourPapers.Sublattice.finiteCoefficientRelation_leading
#print axioms FourPapers.Sublattice.finiteRelationStandard_iff
#print axioms FourPapers.Sublattice.finite_sublattice_rees_groebnerBasis
#print axioms FourPapers.Sublattice.finite_sublattice_rees_kernel
#print axioms FourPapers.Sublattice.finite_sublattice_rees_initialIdeal
#print axioms FourPapers.Sublattice.finiteReesRelations_homogeneous

#print axioms FourPapers.Sublattice.proposition22

end
end
end



end
