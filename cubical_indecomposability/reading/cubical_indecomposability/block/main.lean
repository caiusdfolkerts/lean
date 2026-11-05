import cubical_indecomposability.block.affine_interfaces
import cubical_indecomposability.block.deformations
import cubical_indecomposability.block.parallelepiped
import cubical_indecomposability.elementary_redrawings
import cubical_indecomposability.neighbor_redrawings

/-!
# Proposition 5: the complete auxiliary block

The witness is the paper's rational block in its normalized affine chart.
Every facet, intersection, dimension, face count, and restriction map below
has its ordinary geometric or linear-algebraic definition. The identity
projectivity suffices for the two projective conclusions because the chosen
chart already realizes the stronger affine properties.
-/

set_option autoImplicit false

noncomputable section

namespace CubicalIndecomposability.Block

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes

/-- Proposition 5(v): the distinguished disjoint facet is projectively
equivalent to a nondegenerate three-dimensional parallelepiped. -/
theorem G_projectively_parallelepiped : ProjectivelyParallelepiped G :=
  projectivelyParallelepiped_of_affine G Gcube Gcube_injective Gcube_image_body.symm

/-- Proposition 5 in full, including the genuine quotient-space restriction
claims and the full geometric interface conditions. -/
theorem proposition_five :
    ∃ P : ConvexPolytope 4,
      P.IsFullDim ∧ RationalCoordinates P ∧ IsCubical P ∧
      faceNumber P 0 = 32 ∧ faceNumber P 1 = 80 ∧
      faceNumber P 2 = 72 ∧ faceNumber P 3 = 24 ∧
      ∃ F H G Q : Set (E 4),
      ∃ hF : P.IsFace F, ∃ hH : P.IsFace H, ∃ hG : P.IsFace G,
      ∃ hQ : P.IsFace Q,
        faceDim F = 3 ∧ faceDim H = 3 ∧ faceDim G = 3 ∧
        F ∩ H = Q ∧ faceDim Q = 2 ∧
        (facePolytope P hQ).vertices.card = 4 ∧
        Disjoint G (F ∪ H) ∧
        FaceDetermines P hH ∧ FaceDetermines P hG ∧
        Module.finrank ℝ (deformationRestriction P hF).range ≤ 2 ∧
        HasAffineInterfaceNormalization P F H Q ∧
        ProjectivelyParallelepiped G := by
  exact ⟨polytope, polytope_dimension, rational_coordinates, polytope_isCubical,
    face_vector.1, face_vector.2.1, face_vector.2.2.1, face_vector.2.2.2,
    F, H, G, Q, F_isFace, H_isFace, G_isFace, Q_isFace,
    F_dimension, H_dimension, G_dimension, F_inter_H,
    Q_dimension, Q_vertices_card, G_disjoint_F_union_H,
    H_determines, G_determines, F_restriction_dimension,
    affine_interface_normalization, G_projectively_parallelepiped⟩

end CubicalIndecomposability.Block
