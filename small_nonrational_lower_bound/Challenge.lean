module

public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Rational realizations through ten vertices

Theorem 2 and Corollary 4 of Caius Folkerts' *Small nonrational
four-polytopes* concern rational realizations of ordinary face lattices.
Together with the seventeen-vertex construction they give both the
attainment and numerical bounds on the least size of a nonrational type.

The basic polytope definitions include work of Daniele Cappello, Apache-2.0.
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

/-- A simple vertex has degree equal to the dimension of the polytope. -/
def IsSimpleVertex (P : ConvexPolytope d) (v : VertexType P) : Prop := by
  classical
  exact (polytopeGraph P).degree v = P.dim


end Papers.Polytopes

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes
open scoped Classical

namespace SmallNonrationalBounds

/-- Theorem 2. Every real four-polytope with at most ten extreme vertices
has a rational realization of its ordinary face lattice. -/
theorem theoremTwo (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hn : P.vertices.card ≤ 10) : RationallyRealizable P := by sorry

/-- The minimum in the introduction exists and lies between eleven and
seventeen. Both its attainment and its defining minimality are explicit. -/
theorem minimumVertexBounds :
    ∃ N : ℕ,
      (∃ P : ConvexPolytope 4,
        P.IsFullDim ∧ P.vertices.card = N ∧ ¬ RationallyRealizable P) ∧
      (∀ P : ConvexPolytope 4,
        P.IsFullDim → ¬ RationallyRealizable P → N ≤ P.vertices.card) ∧
      11 ≤ N ∧ N ≤ 17 := by sorry

/-- Corollary 4. An eleven-vertex four-polytope with a simple vertex is
rationally realizable. -/
theorem corollaryFour (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hn : P.vertices.card = 11)
    (hsimple : ∃ v : VertexType P, IsSimpleVertex P v) : RationallyRealizable P := by sorry

end SmallNonrationalBounds
