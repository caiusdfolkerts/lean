import cubical.polytope.graph
import Mathlib.Data.Fintype.BigOperators

/-! # Finite geometric face incidence and double counting -/

open Set
open Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

abbrev DimFaceType (P : ConvexPolytope n) (i : ℕ) :=
  {F : FaceType P // faceDim F.val = i}

abbrev IncidentFaceType (P : ConvexPolytope n) (v : VertexType P) (i : ℕ) :=
  {F : FaceType P // faceDim F.val = i ∧ v.val ∈ F.val}

instance dimFaceTypeFintype (P : ConvexPolytope n) (i : ℕ) : Fintype (DimFaceType P i) :=
  Fintype.ofFinite _

instance incidentFaceTypeFintype (P : ConvexPolytope n) (v : VertexType P) (i : ℕ) :
    Fintype (IncidentFaceType P v i) := Fintype.ofFinite _

def incidentFaceNumber (P : ConvexPolytope n) (v : VertexType P) (i : ℕ) : ℕ :=
  Fintype.card (IncidentFaceType P v i)

theorem card_dimFaceType (P : ConvexPolytope n) (i : ℕ) :
    Fintype.card (DimFaceType P i) = faceNumber P i := by
  classical
  let e : DimFaceType P i ≃ ↥((faceSet P).filter (fun F => faceDim F = i)) :=
    { toFun := fun F => ⟨F.val.val, Finset.mem_filter.mpr ⟨(mem_faceSet P _).mpr F.val.property, F.property⟩⟩
      invFun := fun F => ⟨⟨F.val, (mem_faceSet P _).mp (Finset.mem_filter.mp F.property).1⟩,
        (Finset.mem_filter.mp F.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

theorem incidentFaceNumber_eq (P : ConvexPolytope n) (v : VertexType P) (i : ℕ) :
    incidentFaceNumber P v i =
      ((faceSet P).filter (fun F => faceDim F = i ∧ v.val ∈ F)).card := by
  classical
  let e : IncidentFaceType P v i ≃
      ↥((faceSet P).filter (fun F => faceDim F = i ∧ v.val ∈ F)) :=
    { toFun := fun F => ⟨F.val.val, Finset.mem_filter.mpr ⟨(mem_faceSet P _).mpr F.val.property, F.property⟩⟩
      invFun := fun F => ⟨⟨F.val, (mem_faceSet P _).mp (Finset.mem_filter.mp F.property).1⟩,
        (Finset.mem_filter.mp F.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

/-- A flag consisting of a vertex and an incident face can be indexed in
either order. The vertices remain the actual geometric extreme points. -/
def vertexFaceIncidenceEquiv (P : ConvexPolytope n) (i : ℕ) :
    (Σ v : VertexType P, IncidentFaceType P v i) ≃
      (Σ F : DimFaceType P i, VertexType (facePolytope P F.val.property)) where
  toFun p := ⟨⟨p.2.val, p.2.property.1⟩,
    ⟨p.1.val, Finset.mem_filter.mpr ⟨p.1.property, p.2.property.2⟩⟩⟩
  invFun p := ⟨⟨p.2.val, (Finset.mem_filter.mp p.2.property).1⟩,
    ⟨p.1.val, p.1.property, (Finset.mem_filter.mp p.2.property).2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Double-count incidences between vertices and faces of fixed dimension. -/
theorem sum_incidentFaceNumber (P : ConvexPolytope n) (i : ℕ) :
    ∑ v : VertexType P, incidentFaceNumber P v i =
      ∑ F : DimFaceType P i, (facePolytope P F.val.property).vertices.card := by
  have h := Fintype.card_congr (vertexFaceIncidenceEquiv P i)
  simpa only [Fintype.card_sigma, incidentFaceNumber, VertexType, Fintype.card_coe] using h

theorem sum_incidentFaceNumber_of_uniform_vertices (P : ConvexPolytope n) (i k : ℕ)
    (hvertices : ∀ F : DimFaceType P i,
      (facePolytope P F.val.property).vertices.card = k) :
    ∑ v : VertexType P, incidentFaceNumber P v i = faceNumber P i * k := by
  rw [sum_incidentFaceNumber]
  simp [hvertices, card_dimFaceType]

end LeanEval.Geometry.PlatonicClassification
