module

public import AppendixFacetIdentification
public import ProjectionPolygonBounds

@[expose] public section

/-!
# The exact projection-or-Appendix-B alternative

The projection branch includes the polygon-size hypothesis from
Proposition 7: each polygon avoiding the projection centre has at most four
vertices. The other branch is an ordinary face-order isomorphism with the
convex hull of one of the twelve explicit Appendix B configurations.
-/

noncomputable section
namespace Nonrational.TerminalVerification

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes
open Papers.RationalityTen.ChirotopeDensity
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection

def SatisfiesPaperProjectionCriterion (P : ConvexPolytope 4) : Prop :=
  ∃ (lab : Fin 10 ≃ VertexType P) (B : Boundary 9),
    RealizesBoundary P lab B ∧ Nonempty (PaperCertifiedRelabelling B)

theorem paper_projection_or_explicit_appendix_of_target
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (j : Nat) (hj : j < Nonrational.TerminalData.targetCount)
    (hB : RealizesBoundary P lab (decode (Nonrational.TerminalData.targets j))) :
    SatisfiesPaperProjectionCriterion P ∨ IsExplicitAppendixConfiguration P := by
  rcases targets_classified j hj with h | ⟨a, ha⟩ | himpossible
  · exact Or.inl ⟨lab, decode (Nonrational.TerminalData.targets j), hB,
      paper_certifies_of_certifies j hj h⟩
  · apply Or.inr
    apply explicit_appendix_of_facets P hP
    refine ⟨a, lab, ?_⟩
    intro T
    rw [facetMask_iff_mem_boundary lab hP hB T, ha]
  · exact (himpossible P lab hP hB).elim

#print axioms paper_projection_or_explicit_appendix_of_target

end Nonrational.TerminalVerification
