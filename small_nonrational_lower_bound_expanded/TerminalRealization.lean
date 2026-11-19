module
public import TerminalGeometry
public import Papers.FiniteProjectionHeightCertificate
public import Papers.ActualSharedRelationInterface
public import Papers.SelectedFacetCoreDensity

@[expose] public section

/-! The exact interface from a finite terminal to an ordinary convex polytope.
No abstract incidence system is substituted for `RealizesBoundary`: the
latter identifies both actual facet and actual polygon families. -/
noncomputable section
namespace Nonrational.TerminalVerification

open Nonrational.TerminalData
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes
open Papers.RationalityTen.ChirotopeDensity
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection

def ValidTarget (j : Nat) : Prop :=
  ∀ (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P),
    P.IsFullDim → RealizesBoundary P lab (decode (targets j)) →
      RationallyRealizable P

theorem valid_of_certifies {j : Nat} (h : Certifies j) : ValidTarget j := by
  obtain ⟨C⟩ := h
  intro P lab hP hB
  obtain ⟨Q, φ, hQ, _⟩ := C.rationallyApproximable hP lab hB 1 zero_lt_one
  exact ⟨Q, ⟨φ⟩, hQ⟩

theorem rationallyRealizable_of_matching {j : Nat} (h : ValidTarget j)
    (P : ConvexPolytope 4) (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim)
    (B : Boundary 9) (hB : RealizesBoundary P lab B)
    (σ : Equiv.Perm (Fin 10)) (hmatch : B.relabel σ = decode (targets j)) :
    RationallyRealizable P := by
  apply h P (σ.symm.trans lab) hP
  rw [← hmatch]
  exact hB.relabel σ

/-- The homogeneous supporting-mask predicate and the actual facet-family
predicate agree. This supplies the exact input of the integer witnesses. -/
theorem facetMask_iff_mem_boundary {P : ConvexPolytope 4}
    (lab : Fin 10 ≃ VertexType P) (hP : P.IsFullDim) {B : Boundary 9}
    (hB : RealizesBoundary P lab B) (S : Finset (Fin 10)) :
    FacetMask (vertexCoordinates P lab) S ↔ S ∈ B.facets := by
  constructor
  · intro hS
    obtain ⟨F, hF⟩ := facetMask_actual_three_face P lab S hS
    let f : FacetType P := ⟨⟨F.val.carrier, F.val.isFace⟩,
      F.val.isFace, by rw [F.property, hP]⟩
    exact (hB.facet S).mpr ⟨f, hF⟩
  · intro hS
    obtain ⟨f, hf⟩ := (hB.facet S).mp hS
    have hd : faceDim f.val.val = 3 := by
      have h := f.property.2
      change faceDim f.val.val + 1 = P.dim at h
      rw [hP] at h
      omega
    let F : Papers.PolytopeFaceCounting.Face P 3 :=
      ⟨⟨f.val.val, f.val.property⟩, hd⟩
    have h := actual_three_face_facetMask P hP lab F
    change FacetMask (vertexCoordinates P lab) (faceLabels P lab f.val) at h
    rwa [hf] at h

end Nonrational.TerminalVerification
