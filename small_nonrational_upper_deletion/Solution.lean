module

public import Consolidated.Seventeen
public import Consolidated.DeletionPresentationAndDensity

@[expose] public section
noncomputable section

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

open Papers.Polytopes

namespace SmallNonrational

variable {d : ℕ}

/-- Two vertices correspond under a face-order isomorphism precisely when
their incidences agree on every pair of corresponding faces. -/
def Corresponds {P Q : ConvexPolytope d} (φ : FaceType P ≃o FaceType Q)
    (v : VertexType P) (w : VertexType Q) : Prop :=
  ∀ F : FaceType P, v.val ∈ F.val ↔ w.val ∈ (φ F).val

/-- Near every labelled realization, every vertex can be approximated
simultaneously by the corresponding vertex of a rational realization. -/
def Dense (P : ConvexPolytope d) : Prop :=
  ∀ Q : ConvexPolytope d, CombinatoriallyEquivalent P Q →
    ∀ ε : ℝ, 0 < ε →
      ∃ R : ConvexPolytope d, ∃ φ : FaceType Q ≃o FaceType R,
        RationalCoordinates R ∧ ∀ v : VertexType Q, ∀ w : VertexType R,
          Corresponds φ v w → dist w.val v.val < ε

private theorem corresponds_iff {P Q : ConvexPolytope d} (φ : FaceType P ≃o FaceType Q)
    (v : VertexType P) (w : VertexType Q) : Corresponds φ v w ↔ w = imageVertex φ v := by
  constructor
  · intro h
    have hw := (h (vertexFace P v)).mp (Set.mem_singleton v.val)
    rw [← imageVertex_face φ v] at hw
    exact Subtype.ext (show w.val = (imageVertex φ v).val from hw)
  · rintro rfl F
    exact (imageVertex_mem_iff φ v F).symm

private theorem dense_iff (P : ConvexPolytope d) : Dense P ↔ RationallyDense P := by
  constructor
  · intro h Q hQ ε hε
    obtain ⟨R, φ, hR, hv⟩ := h Q hQ ε hε
    exact ⟨R, φ, hR, fun v => hv v _ ((corresponds_iff φ v _).mpr rfl)⟩
  · intro h Q hQ ε hε
    obtain ⟨R, φ, hR, hv⟩ := h Q hQ ε hε
    refine ⟨R, φ, hR, ?_⟩
    intro v w hw
    rw [(corresponds_iff φ v w).mp hw]
    exact hv v

/-- Theorem 1. A seventeen-vertex four-polytope has a realization over a
real subfield precisely when the field contains the square root of five. -/
theorem theoremOne :
    ∃ P : ConvexPolytope 4, P.IsFullDim ∧ P.vertices.card = 17 ∧
      ∀ K : Subfield ℝ, RealizableOver P K ↔ Real.sqrt 5 ∈ K := Papers.Nonrational.Seventeen.seventeen_vertex_field_theorem

/-- The seventeen-vertex construction has no rational realization. -/
theorem seventeenVertexNonrational :
    ∃ P : ConvexPolytope 4,
      P.IsFullDim ∧ P.vertices.card = 17 ∧ ¬ RationallyRealizable P := Papers.Nonrational.Seventeen.exists_seventeen_vertex_nonrational_polytope

/-- Theorem 3. Deleting a simple vertex of a nonsimplex gives a polytope
of the same dimension, determined by the marked face lattice. Its realization
fields and the density of rational realizations agree with those before deletion. -/
theorem theoremThree (d : ℕ) (P : ConvexPolytope d) (v : VertexType P)
    (hP : P.IsFullDim) (hcard : d + 1 < P.vertices.card)
    (hs : IsSimpleVertex P v) :
    ∃ hne : (P.vertices.erase v.val).Nonempty,
      (deleteVertex P v.val hne).IsFullDim ∧
      (∀ (Q : ConvexPolytope d) (φ : FaceType P ≃o FaceType Q)
          (w : VertexType Q), Corresponds φ v w →
          ∀ hneQ : (Q.vertices.erase w.val).Nonempty,
            CombinatoriallyEquivalent (deleteVertex P v.val hne)
              (deleteVertex Q w.val hneQ)) ∧
      realizationFields P = realizationFields (deleteVertex P v.val hne) ∧
      (Dense P ↔ Dense (deleteVertex P v.val hne)) := by
  obtain ⟨hne, hdim, htype, hfields, hdense⟩ :=
    paper_simple_vertex_deletion d P v hP hcard hs
  refine ⟨hne, hdim, ?_, hfields, (dense_iff P).trans (hdense.trans (dense_iff _).symm)⟩
  intro Q φ w hw hneQ
  obtain rfl := (corresponds_iff φ v w).mp hw
  exact htype Q φ hneQ

end SmallNonrational
