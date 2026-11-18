module

public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Realization fields of convex polytopes

Theorem 1 of Caius Folkerts' *Small nonrational four-polytopes* realizes
exactly the real fields containing the golden quadratic field on one
seventeen-vertex face lattice. Theorem 3 treats any simple vertex of a
nonsimplex in any dimension. Its deletion preserves the realization fields
and the density of rational labelled realizations. The nonrationality
consequence concerns every realization of the seventeen-vertex face lattice.

The polytope structure and its basic geometric definitions below are adapted
from Daniele Cappello's Lean polytope foundations, licensed under Apache-2.0.
-/

@[expose] public section
noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

/-- The Euclidean model space `ℝⁿ`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A **convex polytope** in `ℝⁿ`: the convex hull of a finite nonempty set
whose listed vertices are exactly the extreme points of the hull. -/
structure ConvexPolytope (n : ℕ) where
  vertices : Finset (E n)
  vertices_nonempty : vertices.Nonempty
  vertices_eq_extremePoints :
    (vertices : Set (E n)) =
      Set.extremePoints ℝ (convexHull ℝ ((vertices : Set (E n))))

namespace ConvexPolytope

/-- The underlying convex set of the polytope. -/
def toSet {n : ℕ} (P : ConvexPolytope n) : Set (E n) :=
  convexHull ℝ ((P.vertices : Set (E n)))

/-- The affine dimension of `P`. -/
noncomputable def dim {n : ℕ} (P : ConvexPolytope n) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ P.toSet)

/-- `P` is **full-dimensional** if `dim P = n`. -/
def IsFullDim {n : ℕ} (P : ConvexPolytope n) : Prop := P.dim = n

/-- A **face** of `P` is a nonempty exposed subset. -/
def IsFace {n : ℕ} (P : ConvexPolytope n) (F : Set (E n)) : Prop :=
  IsExposed ℝ P.toSet F ∧ F.Nonempty

/-- The affine dimension of a subset of `ℝⁿ`. -/
noncomputable def faceDim {n : ℕ} (F : Set (E n)) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ F)

end ConvexPolytope

open ConvexPolytope
variable {n : ℕ}

/-- The nonempty geometric face poset, ordered by inclusion. -/
abbrev FaceType (P : ConvexPolytope n) := {F : Set (E n) // P.IsFace F}

/-- Vertices of a geometric convex polytope. -/
abbrev VertexType (P : ConvexPolytope n) := {v : E n // v ∈ P.vertices}

/-- The ordinary graph of vertices and edges of a convex polytope. -/
def polytopeGraph (P : ConvexPolytope n) : SimpleGraph (VertexType P) where
  Adj u v := u ≠ v ∧ ∃ F : Set (E n),
    P.IsFace F ∧ faceDim F = 1 ∧ u.val ∈ F ∧ v.val ∈ F
  symm := by
    constructor
    rintro u v ⟨hne, F, hF, hdF, hu, hv⟩
    exact ⟨hne.symm, F, hF, hdF, hv, hu⟩
  loopless := by
    constructor
    intro u h
    exact h.1 rfl

end LeanEval.Geometry.PlatonicClassification

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

namespace Papers.Polytopes

variable {d : ℕ}

/-- Isomorphism of the nonempty faces under inclusion. Adjoining the empty
face to both posets gives the ordinary complete face lattices. -/
def CombinatoriallyEquivalent (P Q : ConvexPolytope d) : Prop :=
  Nonempty (FaceType P ≃o FaceType Q)

/-- Every coordinate of every vertex lies in the given real subfield. -/
def CoordinatesIn (K : Subfield ℝ) (P : ConvexPolytope d) : Prop :=
  ∀ v ∈ P.vertices, ∀ i : Fin d, v i ∈ K

/-- Every vertex has rational coordinates. -/
def RationalCoordinates (P : ConvexPolytope d) : Prop :=
  ∀ v ∈ P.vertices, ∀ i : Fin d, ∃ q : ℚ, (q : ℝ) = v i

/-- The face lattice admits a realization with all vertex coordinates in K. -/
def RealizableOver (P : ConvexPolytope d) (K : Subfield ℝ) : Prop :=
  ∃ Q : ConvexPolytope d, CombinatoriallyEquivalent P Q ∧ CoordinatesIn K Q

/-- The face lattice admits a realization over the rationals. -/
def RationallyRealizable (P : ConvexPolytope d) : Prop :=
  ∃ Q : ConvexPolytope d, CombinatoriallyEquivalent P Q ∧ RationalCoordinates Q

/-- The convex hull of a nonempty subset of the extreme vertices. -/
def vertexSubsetPolytope (P : ConvexPolytope d) (S : Finset (E d))
    (hne : S.Nonempty) (hsub : S ⊆ P.vertices) : ConvexPolytope d where
  vertices := S
  vertices_nonempty := hne
  vertices_eq_extremePoints := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxP : x ∈ P.vertices := hsub hx
      have hxext : x ∈ P.toSet.extremePoints ℝ := by
        change x ∈ (convexHull ℝ (P.vertices : Set (E d))).extremePoints ℝ
        rw [← P.vertices_eq_extremePoints]
        exact hxP
      have hhull : convexHull ℝ (S : Set (E d)) ⊆ P.toSet := by
        apply convexHull_mono
        exact hsub
      exact inter_extremePoints_subset_extremePoints_of_subset hhull
        ⟨subset_convexHull ℝ _ hx, hxext⟩
    · exact extremePoints_convexHull_subset

/-- The convex hull of the vertices remaining after erasing the given point. -/
def deleteVertex (P : ConvexPolytope d) (v : E d)
    (hne : (P.vertices.erase v).Nonempty) : ConvexPolytope d :=
  vertexSubsetPolytope P (P.vertices.erase v) hne (Finset.erase_subset _ _)

/-- A simple vertex has degree equal to the dimension of the polytope. -/
def IsSimpleVertex (P : ConvexPolytope d) (v : VertexType P) : Prop := by
  classical
  exact (polytopeGraph P).degree v = P.dim

/-- The real subfields over which this face lattice has a realization. -/
def realizationFields (P : ConvexPolytope d) : Set (Subfield ℝ) :=
  {K | RealizableOver P K}

end Papers.Polytopes

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

/-- Theorem 1. A seventeen-vertex four-polytope has a realization over a
real subfield precisely when the field contains the square root of five. -/
theorem theoremOne :
    ∃ P : ConvexPolytope 4, P.IsFullDim ∧ P.vertices.card = 17 ∧
      ∀ K : Subfield ℝ, RealizableOver P K ↔ Real.sqrt 5 ∈ K := by sorry

/-- The seventeen-vertex construction has no rational realization. -/
theorem seventeenVertexNonrational :
    ∃ P : ConvexPolytope 4,
      P.IsFullDim ∧ P.vertices.card = 17 ∧ ¬ RationallyRealizable P := by sorry

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
      (Dense P ↔ Dense (deleteVertex P v.val hne)) := by sorry

end SmallNonrational
