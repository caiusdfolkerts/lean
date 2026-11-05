module
public import Consolidated.ProjectionCertificateSoundness
public import FaceOrderExcessInvariants
public import Consolidated.RankFourTheorems
public import Consolidated.SixActualAssembly
public import Papers.GlobalEightRelationRowsClosed

set_option autoImplicit false

section DensityPart0
/- Original interface: Papers.ProjectionTypeDensity. -/
@[expose] public section

/-!
# Projection certificates imply density of the entire combinatorial type

The projection and height rules depend on complete labelled facet and polygon
families. Those families transport through an ordinary face-order isomorphism,
so one combinatorial certificate applies near every realization of the type.
There is no restriction on the number of vertices or height rows.
-/

noncomputable section
set_option autoImplicit false

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting

/-- Transported vertex labels retain exactly the labels on each actual face. -/
theorem faceLabels_of_faceOrder {n : ℕ} {P Q : ConvexPolytope 4}
    (φ : FaceType P ≃o FaceType Q) (lab : Fin (n + 1) ≃ VertexType P)
    (F : FaceType P) :
    faceLabels Q (lab.trans (vertexEquivOfFaceOrder φ)) (φ F) =
      faceLabels P lab F := by
  ext i
  rw [mem_faceLabels, mem_faceLabels]
  exact imageVertex_mem_iff φ (lab i) F

/-- A complete literal boundary describes every realization of its face type,
with the vertex names induced by the face-order isomorphism. -/
theorem RealizesBoundary.transport {n : ℕ} {P Q : ConvexPolytope 4}
    {lab : Fin (n + 1) ≃ VertexType P} {B : Boundary n}
    (h : RealizesBoundary P lab B) (φ : FaceType P ≃o FaceType Q) :
    RealizesBoundary Q (lab.trans (vertexEquivOfFaceOrder φ)) B := by
  let eF := facetEquivOfFaceOrder φ
  let eR : Face P 2 ≃ Face Q 2 := rankedFaceEquivOfFaceOrder φ
  constructor
  · intro S
    rw [h.facet S]
    constructor
    · rintro ⟨F, hF⟩
      exact ⟨eF F, (faceLabels_of_faceOrder φ lab F.val).trans hF⟩
    · rintro ⟨G, hG⟩
      refine ⟨eF.symm G, ?_⟩
      calc
        faceLabels P lab (eF.symm G).val =
            faceLabels Q (lab.trans (vertexEquivOfFaceOrder φ))
              (eF (eF.symm G)).val :=
          (faceLabels_of_faceOrder φ lab (eF.symm G).val).symm
        _ = faceLabels Q (lab.trans (vertexEquivOfFaceOrder φ)) G.val := by
          rw [eF.apply_symm_apply]
        _ = S := hG
  · intro S
    rw [h.polygon S]
    constructor
    · rintro ⟨R, hR⟩
      exact ⟨eR R, (actualFaceLabels_of_faceOrder φ lab R).trans hR⟩
    · rintro ⟨T, hT⟩
      refine ⟨eR.symm T, ?_⟩
      calc
        actualFaceLabels P lab (eR.symm T).val =
            actualFaceLabels Q (lab.trans (vertexEquivOfFaceOrder φ))
              (eR (eR.symm T)).val :=
          (actualFaceLabels_of_faceOrder φ lab (eR.symm T)).symm
        _ = actualFaceLabels Q (lab.trans (vertexEquivOfFaceOrder φ)) T.val := by
          rw [eR.apply_symm_apply]
        _ = S := hT

/-- Proposition 7 in its whole-type form. The record contains the incidence
rule deletion order, the certified height pivots, and the prescribed facet
relations. The geometric hypotheses are verified anew at every realization. -/
theorem ReconstructionCertificate.rationallyDense {n c : ℕ} {B : Boundary n}
    (K : ReconstructionCertificate B c) {P : ConvexPolytope 4}
    (hP : P.IsFullDim) (lab : Fin (n + 1) ≃ VertexType P)
    (hB : RealizesBoundary P lab B) : RationallyDense P := by
  rintro Q ⟨φ⟩
  have hQ : Q.IsFullDim := (faceOrderIso_polytope_dim φ).trans hP
  exact actual_labelled_polytope_rationallyApproximable_of_finite_projection_certificate
    hQ (lab.trans (vertexEquivOfFaceOrder φ)) B (hB.transport φ) K

/-- The same conclusion after an arbitrary certified permutation of labels.
The distinguished projection vertex therefore imposes no labelling restriction. -/
theorem CertifiedRelabelling.rationallyDense {n : ℕ} {B : Boundary n}
    (C : CertifiedRelabelling B) {P : ConvexPolytope 4} (hP : P.IsFullDim)
    (lab : Fin (n + 1) ≃ VertexType P) (hB : RealizesBoundary P lab B) :
    RationallyDense P := by
  rintro Q ⟨φ⟩
  have hQ : Q.IsFullDim := (faceOrderIso_polytope_dim φ).trans hP
  exact C.rationallyApproximable hQ (lab.trans (vertexEquivOfFaceOrder φ))
    (hB.transport φ)

#print axioms RealizesBoundary.transport
#print axioms ReconstructionCertificate.rationallyDense
#print axioms CertifiedRelabelling.rationallyDense

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection

end
end
end DensityPart0

section DensityPart1
/- Original interface: Papers.DensityTheorems. -/
@[expose] public section

/-!
# Proposition 8: the closed density statements

The matrix classification is supplied by its proved theorem. The vertex and
facet alternatives have no bound on the total size of the other face sets.
The third alternative is the global statement for a type admitting one
realization with the required relation-row bound.
-/

noncomputable section
namespace Papers.CheckedDensity

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFacetSurplus
open Papers.RationalityTen.ChirotopeDensity
open Papers.RationalityTen.PrincipalGeometryAssembly
open Papers.RationalityTen.MatroidChecked.MatrixClassificationAssembly

/-- Proposition 8(i), including approximation at every equivalent realization. -/
theorem proposition_eight_i (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hn : P.vertices.card ≤ 9) : RationallyDense P :=
  proposition_eight_i_of_inputs nine_column_exceptional_matrix_density P hP hn

/-- Proposition 8(ii), with both alternatives and no additional size bound. -/
theorem proposition_eight_ii (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hcount : (nonsimplicialFacets P).card ≤ 9 ∨ (nonsimpleVertices P).card ≤ 9) :
    RationallyDense P :=
  proposition_eight_ii_of_inputs nine_column_exceptional_matrix_density P hP hcount

#print axioms proposition_eight_i
#print axioms proposition_eight_ii

end Papers.CheckedDensity

end
end
end DensityPart1
