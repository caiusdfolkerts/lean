module
public import Lean.Elab.Tactic.Omega
public import Papers.ActualFaceFiniteness
public import Papers.ActualNeighborBound

@[expose] public section

/-!
# Counting two-faces incident to an actual edge

The generic counting lemma below consumes an actual vertex-figure neighbor
embedding.  Constructing that embedding from the checked vertex-slice face
correspondence is a separate geometric step; this file does not substitute the
existence of such an embedding for the desired unconditional theorem.
-/

namespace Papers.Polytopes

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d e : ℕ}

/-- Actual nonempty two-faces containing both endpoints of an edge. -/
noncomputable def incidentTwoFaces (P : ConvexPolytope d) (x y : E d) :
    Finset (ActualFaceType P) := by
  classical
  exact Finset.univ.filter fun F => faceDim F.val = 2 ∧ x ∈ F.val ∧ y ∈ F.val

/-- The dimension bound follows from the usual degree bound in the vertex
figure and an injection of actual neighboring vertices into incident two-faces. -/
theorem incidentTwoFaces_card_from_vertexFigure
    (P : ConvexPolytope d) (x y : E d)
    (Q : ConvexPolytope e) (q : E e) (hq : q ∈ Q.vertices)
    (hdim : Q.dim + 1 = P.dim)
    (lift : (Papers.PolytopeVertexCone.actualNeighbors Q q) → incidentTwoFaces P x y)
    (hlift : Function.Injective lift) :
    P.dim ≤ (incidentTwoFaces P x y).card + 1 := by
  classical
  have hdegree := actual_neighbor_card_ge_dim Q hq
  have hcard : (Papers.PolytopeVertexCone.actualNeighbors Q q).card ≤ (incidentTwoFaces P x y).card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective lift hlift
  omega

theorem incidentTwoFaces_card_from_vertexFigure_fullDim
    (P : ConvexPolytope d) (hP : P.IsFullDim) (x y : E d)
    (Q : ConvexPolytope e) (q : E e) (hq : q ∈ Q.vertices)
    (hdim : Q.dim + 1 = P.dim)
    (lift : (Papers.PolytopeVertexCone.actualNeighbors Q q) → incidentTwoFaces P x y)
    (hlift : Function.Injective lift) :
    d - 1 ≤ (incidentTwoFaces P x y).card := by
  have h := incidentTwoFaces_card_from_vertexFigure P x y Q q hq hdim lift hlift
  change P.dim = d at hP
  omega

end Papers.Polytopes

