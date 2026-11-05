module

public import FaceOrderNumericalInvariants
public import Consolidated.SmallPolytopeBudgets

@[expose] public section

/-! The excesses used in the global eight-row argument depend only on the
ordinary face order. The proof transports each actual polygon and its vertex
set; it makes no assertion about the ranks of its relation spaces. -/

noncomputable section
namespace Papers.RationalityTen.ChirotopeDensity

open Finset Set
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeIncidenceCounting
open Papers.PolytopeRelationBudget Papers.PolytopeFacetSurplus Papers.PolytopeFaceRestriction

def faceBelowEquivOfFaceOrder {d e k l : Nat}
    {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (F : Face P k) :
    FaceBelow P F.val.carrier l ≃
      FaceBelow Q ((rankedFaceEquivOfFaceOrder φ) F).val.carrier l :=
  Equiv.subtypeEquiv (rankedFaceEquivOfFaceOrder φ) (by
    intro R
    change (R.val.carrier ⊆ F.val.carrier) ↔
      ((φ ⟨R.val.carrier, R.val.isFace⟩).val ⊆ (φ ⟨F.val.carrier, F.val.isFace⟩).val)
    change ((⟨R.val.carrier, R.val.isFace⟩ : FaceType P) ≤
      ⟨F.val.carrier, F.val.isFace⟩) ↔
      (φ ⟨R.val.carrier, R.val.isFace⟩ ≤ φ ⟨F.val.carrier, F.val.isFace⟩)
    exact φ.le_iff_le.symm)

/-- Choose the labels of the second realization from the vertex
correspondence, so every actual face keeps exactly the same labels. -/
theorem actualFaceLabels_of_faceOrder {d e n k : Nat}
    {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (lab : Fin n ≃ P.vertices) (F : Face P k) :
    actualFaceLabels Q (lab.trans (vertexEquivOfFaceOrder φ))
        ((rankedFaceEquivOfFaceOrder φ) F).val = actualFaceLabels P lab F.val := by
  ext i
  rw [mem_actualFaceLabels, mem_actualFaceLabels]
  exact imageVertex_mem_iff φ (lab i) ⟨F.val.carrier, F.val.isFace⟩

theorem polygonLabelsBelow_of_faceOrder {d e n : Nat}
    {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (lab : Fin n ≃ P.vertices) (F : Face P 3) :
    polygonLabelsBelow Q (lab.trans (vertexEquivOfFaceOrder φ))
        ((rankedFaceEquivOfFaceOrder φ) F) = polygonLabelsBelow P lab F := by
  let b := faceBelowEquivOfFaceOrder (l := 2) φ F
  ext S
  constructor
  · intro hS
    obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hS
    refine Finset.mem_image.mpr ⟨b.symm R, Finset.mem_univ _, ?_⟩
    calc
      actualFaceLabels P lab (b.symm R).val.val =
          actualFaceLabels Q (lab.trans (vertexEquivOfFaceOrder φ))
            (b (b.symm R)).val.val :=
        (actualFaceLabels_of_faceOrder φ lab (b.symm R).val).symm
      _ = _ := congrArg
        (fun T => actualFaceLabels Q (lab.trans (vertexEquivOfFaceOrder φ)) T.val.val)
        (b.apply_symm_apply R)
  · intro hS
    obtain ⟨R, _, rfl⟩ := Finset.mem_image.mp hS
    exact Finset.mem_image.mpr ⟨b R, Finset.mem_univ _,
      actualFaceLabels_of_faceOrder φ lab R.val⟩

theorem facetPolygonExcess_of_faceOrder {d e : Nat}
    {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (F : Face P 3) :
    facetPolygonExcess P F = facetPolygonExcess Q ((rankedFaceEquivOfFaceOrder φ) F) := by
  rw [facetPolygonExcess_eq_sum_faceBelow, facetPolygonExcess_eq_sum_faceBelow]
  let b := faceBelowEquivOfFaceOrder (l := 2) φ F
  calc
    _ = ∑ R : FaceBelow P F.val.carrier 2,
        ((Nat.card (VerticesOn Q (b R).val.val.carrier) : Int) - 3) := by
      apply Finset.sum_congr rfl
      intro R _
      exact congrArg (fun n : Nat => (n : Int) - 3)
        (ranked_face_vertices_card_of_faceOrder φ R.val)
    _ = _ := Equiv.sum_comp b (fun R : FaceBelow Q
      ((rankedFaceEquivOfFaceOrder φ) F).val.carrier 2 =>
        ((Nat.card (VerticesOn Q R.val.val.carrier) : Int) - 3))

theorem facetExcess_of_faceOrder {d e : Nat}
    {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) : facetExcess P = facetExcess Q := by
  unfold facetExcess
  calc
    _ = ∑ F : Face P 3,
        ((Nat.card (VerticesOn Q ((rankedFaceEquivOfFaceOrder φ) F).val.carrier) : Int) - 4) := by
      apply Finset.sum_congr rfl
      intro F _
      rw [ranked_face_vertices_card_of_faceOrder φ F]
    _ = _ := Equiv.sum_comp (rankedFaceEquivOfFaceOrder φ)
      (fun F : Face Q 3 => ((Nat.card (VerticesOn Q F.val.carrier) : Int) - 4))

theorem polygonExcess_of_faceOrder {d e : Nat}
    {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) : polygonExcess P = polygonExcess Q := by
  unfold polygonExcess
  calc
    _ = ∑ R : Face P 2,
        ((Nat.card (VerticesOn Q ((rankedFaceEquivOfFaceOrder φ) R).val.carrier) : Int) - 3) := by
      apply Finset.sum_congr rfl
      intro R _
      rw [ranked_face_vertices_card_of_faceOrder φ R]
    _ = _ := Equiv.sum_comp (rankedFaceEquivOfFaceOrder φ)
      (fun R : Face Q 2 => ((Nat.card (VerticesOn Q R.val.carrier) : Int) - 3))

#print axioms facetPolygonExcess_of_faceOrder
#print axioms polygonLabelsBelow_of_faceOrder
#print axioms facetExcess_of_faceOrder
#print axioms polygonExcess_of_faceOrder

end Papers.RationalityTen.ChirotopeDensity
