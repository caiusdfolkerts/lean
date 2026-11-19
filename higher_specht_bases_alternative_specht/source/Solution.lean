module

public import higher_specht.verified.remaining03_complete

@[expose] public section
noncomputable section
open TauCeti MvPolynomial

namespace HigherSpecht.GriffinIdealExpression
variable {n s : ℕ}

theorem alternative_specht_spans
    (e : GriffinIdealExpression n s) (hs : 0 < s) (f : YoungDiagram → PolynomialRing n ℂ)
    (hf : ∀ j : {j : FiniteHarmonicIndex n s // j ∈ e.eligible},
      IsDominanceTriangularMultiplier n j.val.multiplier (f j.val.multiplier))
    (i : {i : FiniteHarmonicIndex n s // i ∈ e.eligible}) :
    ∃ W : Subrepresentation (quotientRepresentation (e.ideal ℂ) (e.permutationStable ℂ)),
      W.toSubmodule =
        Submodule.span ℂ (Set.range fun T : StandardYoungTableau (YoungDiagram.ofPartition i.val.part) =>
          e.alternativeFamily f ⟨i, T⟩) ∧
      W.toRepresentation.IsIrreducible ∧
      Nonempty (Representation.Equiv (partitionSpechtRepresentationOver ℂ i.val.part)
        W.toRepresentation) :=
  ⟨e.alternativeCopyOnEligible f hf i, e.corollary_5_3_alternative_copy_onEligible f hf hs i⟩

end HigherSpecht.GriffinIdealExpression
