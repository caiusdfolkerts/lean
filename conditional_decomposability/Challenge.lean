module
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# The sharp vertex bound for conditional Minkowski decomposability

Theorem 1 of Caius Folkerts, *The sharp vertex bound for conditional
 decomposability* (paper.pdf): in every dimension d >= 3 the least vertex
count of a conditionally decomposable d-polytope is 4d-4. Below this count,
Minkowski decomposability is determined by the face lattice.

The definitions below are independent, verbatim semantic copies of the
specified public definitions in the substantive development. In particular,
polytopes are actual finite convex hulls with exactly their extreme vertices,
faces are nonempty exposed faces ordered by inclusion, and summands may have
any affine dimension. The omitted empty face can be adjoined as a bottom
without changing the notion of face-poset equivalence.

Provenance: the geometric model is adapted from Daniele Cappello's
SolarYs431/lean-eval-platonic-classification (Apache-2.0); original source
headers, project NOTICE, and third-party licences are retained in source/.
No project-specific source is imported by this Challenge.
-/

@[expose] public section
noncomputable section
open Set
open scoped Pointwise

namespace LeanEval.Geometry.PlatonicClassification

/-- Euclidean n-space, with Mathlib's usual real inner product. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A nonempty finite convex hull, listed by exactly its extreme vertices. -/
structure ConvexPolytope (n : ℕ) where
  vertices : Finset (E n)
  vertices_nonempty : vertices.Nonempty
  vertices_eq_extremePoints :
    (vertices : Set (E n)) =
      Set.extremePoints ℝ (convexHull ℝ ((vertices : Set (E n))))

namespace ConvexPolytope
/-- The actual underlying convex set. -/
def toSet {n : ℕ} (P : ConvexPolytope n) : Set (E n) :=
  convexHull ℝ ((P.vertices : Set (E n)))
/-- Affine dimension, as the dimension of the vector span of differences. -/
noncomputable def dim {n : ℕ} (P : ConvexPolytope n) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ P.toSet)
/-- Full dimension in the specified ambient Euclidean space. -/
def IsFullDim {n : ℕ} (P : ConvexPolytope n) : Prop := P.dim = n
/-- An ordinary nonempty exposed face of this finite convex polytope. -/
def IsFace {n : ℕ} (P : ConvexPolytope n) (F : Set (E n)) : Prop :=
  IsExposed ℝ P.toSet F ∧ F.Nonempty
end ConvexPolytope

/-- Nonempty faces, carrying the inherited inclusion order. -/
abbrev FaceType {n : ℕ} (P : ConvexPolytope n) := {F : Set (E n) // P.IsFace F}
end LeanEval.Geometry.PlatonicClassification

namespace Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {d : ℕ}

/-- Face-lattice equivalence, represented by the nonempty face posets. -/
def CombinatoriallyEquivalent (P Q : ConvexPolytope d) : Prop :=
  Nonempty (FaceType P ≃o FaceType Q)
/-- Positive homothety of the actual convex sets; translations are allowed. -/
def IsHomotheticCopy (P A : ConvexPolytope d) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ b : E d,
    A.toSet = (fun x : E d => r • x + b) '' P.toSet
/-- A Minkowski sum of two polytopes, neither a positive homothetic copy. -/
def MinkowskiDecomposable (P : ConvexPolytope d) : Prop :=
  ∃ A B : ConvexPolytope d,
    P.toSet = A.toSet + B.toSet ∧
    ¬IsHomotheticCopy P A ∧ ¬IsHomotheticCopy P B
/-- The face lattice admits both decomposable and indecomposable realizations. -/
def ConditionallyDecomposable (P : ConvexPolytope d) : Prop :=
  (∃ Q : ConvexPolytope d, CombinatoriallyEquivalent P Q ∧ MinkowskiDecomposable Q) ∧
  (∃ Q : ConvexPolytope d, CombinatoriallyEquivalent P Q ∧ ¬MinkowskiDecomposable Q)

/-- Theorem 1: universal lower bound and attainment in every d >= 3. -/
theorem conditional_decomposability_sharp (d : ℕ) (hd : 3 ≤ d) :
    (∀ P : ConvexPolytope d, P.IsFullDim → ConditionallyDecomposable P →
      4*d-4 ≤ P.vertices.card) ∧
    (∃ P : ConvexPolytope d, P.IsFullDim ∧ ConditionallyDecomposable P ∧
      P.vertices.card=4*d-4) := by sorry

/-- The literal least number of vertices of a conditionally decomposable polytope. -/
theorem conditional_vertex_count_isLeast (d : ℕ) (hd : 3 ≤ d) :
    IsLeast {N : ℕ | ∃ P : ConvexPolytope d,
      P.IsFullDim ∧ ConditionallyDecomposable P ∧ P.vertices.card=N} (4*d-4) := by sorry

/-- The stronger assertion following Theorem 1: decomposability persists in
all realizations of a face lattice with at most 4d-5 vertices. -/
theorem decomposability_determined_by_face_lattice_below_threshold
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (hN : P.vertices.card ≤ 4*d-5) (hdecomp : MinkowskiDecomposable P)
    (Q : ConvexPolytope d) (hPQ : CombinatoriallyEquivalent P Q) :
    MinkowskiDecomposable Q := by sorry

/-- Decomposability is simultaneous in face-equivalent realizations below threshold. -/
theorem decomposable_iff_of_face_iso_below_threshold
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3≤d)
    (hN : P.vertices.card≤4*d-5)
    (Q : ConvexPolytope d) (hPQ : CombinatoriallyEquivalent P Q) :
    MinkowskiDecomposable P ↔ MinkowskiDecomposable Q := by sorry

/-- The sharp examples have exactly 4d-4 vertices in every d >= 3. -/
theorem conditional_decomposability_attainment (d : ℕ) (hd : 3 ≤ d) :
    ∃ P : ConvexPolytope d, P.IsFullDim ∧ ConditionallyDecomposable P ∧
      P.vertices.card = 4 * d - 4 := by sorry

end Papers.Polytopes
