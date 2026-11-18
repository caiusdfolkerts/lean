module
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Analysis.Convex.SimplicialComplex.AffineIndependentUnion
public import Mathlib.Analysis.Convex.StdSimplex
/-!
# Face numbers of cubical polytopes

Theorem 1 gives the exact cubical edge lower bound in every dimension at
least three, with its bipartition-imbalance strengthening in dimensions at
least four. Corollary 4 extends the strengthened bound to every finite cubical
PL sphere; the sphere condition is an actual piecewise affine equivalence of
the face-chain realization to a simplex boundary. Corollary 5 gives all the
higher face bounds. Cubes and every finite realized stacking sequence attain
the bounds. No numerical inequality or rigidity assertion occurs in the
custom geometric, cubical, PL-sphere, or stacking definitions below.

All custom mathematical data are independently copied with their exact
original semantics and names. Construction well-formedness proofs alone are
Challenge holes. The complete source preserves Apache-2.0 attribution to
Daniele Cappello and DifferentialGeometry contributors.
-/
@[expose] public section
noncomputable section
open Set
open scoped Pointwise Classical Topology BigOperators
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


namespace LeanEval.Geometry.PlatonicClassification
open ConvexPolytope
variable {n : ℕ}
/-- Affine dimension of a geometric face. -/
noncomputable def ConvexPolytope.faceDim {n : ℕ} (F : Set (E n)) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ F)
/-- Every actual finite convex polytope has only finitely many exposed faces. -/
theorem finite_isFace (P : ConvexPolytope n) :
    Set.Finite {F : Set (E n) | P.IsFace F} := by sorry
/-- All nonempty geometric faces. -/
noncomputable def faceSet (P : ConvexPolytope n) : Finset (Set (E n)) :=
  (finite_isFace P).toFinset
/-- The literal number of geometric faces of affine dimension i. -/
noncomputable def faceNumber (P : ConvexPolytope n) (i : ℕ) : ℕ := by
  classical
  exact ((faceSet P).filter (fun F => faceDim F = i)).card
/-- The face as a convex polytope, with its actual extreme vertices. -/
noncomputable def facePolytope (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) : ConvexPolytope n where
  vertices := P.vertices.filter (· ∈ f)
  vertices_nonempty := by sorry
  vertices_eq_extremePoints := by sorry
/-- A sign vector of the standard geometric cube. -/
noncomputable def vertIper {d : ℕ} (s : Fin d → Bool) : E d :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => if s i then 1 else -1)
/-- The set of all 2^d cube vertices. -/
noncomputable def verticiIper (d : ℕ) : Finset (E d) :=
  (Finset.univ : Finset (Fin d → Bool)).image vertIper
/-- The convex hull of all sign vectors, including the zero-dimensional cube. -/
noncomputable def standardCube (d : ℕ) : ConvexPolytope d :=
  ⟨verticiIper d, by sorry, by sorry⟩
/-- Combinatorial equivalence via the ordinary nonempty geometric face posets. -/
def CombinatoriallyEquivalent {n m : ℕ}
    (P : ConvexPolytope n) (Q : ConvexPolytope m) : Prop :=
  Nonempty (FaceType P ≃o FaceType Q)
/-- Every geometric facet has the face poset of a cube of the required dimension. -/
def IsCubical {n : ℕ} (P : ConvexPolytope n) : Prop :=
  ∀ (F : Set (E n)) (hF : P.IsFace F),
    faceDim F + 1 = P.dim →
    CombinatoriallyEquivalent (facePolytope P hF) (standardCube (P.dim - 1))
/-- Oriented actual edge relation between distinct vertices of a polytope. -/
def GeneralVertexStep (P : ConvexPolytope n) (p q : E n) : Prop :=
  q ∈ P.vertices ∧ p ≠ q ∧
    ∃ e : Set (E n), P.IsFace e ∧ faceDim e = 1 ∧ p ∈ e ∧ q ∈ e
end LeanEval.Geometry.PlatonicClassification


namespace Cubical.Bipartite
variable {V : Type*} {G : SimpleGraph V}
/-- Vertices in the false colour class of a proper bipartition. -/
abbrev Black (c : G.Coloring Bool) := {v : V // c v = false}
/-- Vertices in the true colour class of a proper bipartition. -/
abbrev White (c : G.Coloring Bool) := {v : V // c v = true}
end Cubical.Bipartite

namespace LeanEval.Geometry.PlatonicClassification
open ConvexPolytope Cubical.Bipartite
variable {n m : ℕ}
/-- Actual extreme vertices as a finite type. -/
abbrev VertexType (P : ConvexPolytope n) := {v : E n // v ∈ P.vertices}
/-- The actual graph of one-dimensional exposed faces. -/
def polytopeGraph (P : ConvexPolytope n) : SimpleGraph (VertexType P) where
  Adj u v := u ≠ v ∧ ∃ F : Set (E n),
    P.IsFace F ∧ faceDim F = 1 ∧ u.val ∈ F ∧ v.val ∈ F
  symm := by sorry
  loopless := by sorry
/-- Actual facets are the codimension-one faces. -/
abbrev FacetType (P : ConvexPolytope n) :=
  {F : FaceType P // faceDim F.val + 1 = P.dim}

/-- Theorem 1 in the paper's real-valued notation. -/
theorem IsCubical.edge_bound (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 3 ≤ P.dim) :
    ((P.dim : ℝ) + 1) / 2 * P.vertices.card - 2 ^ (P.dim - 1) ≤ faceNumber P 1 := by sorry

/-- Theorem 1 with exact integral scaling. -/
theorem IsCubical.edge_bound_nat (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 3 ≤ P.dim) :
    (P.dim + 1) * P.vertices.card ≤ 2 * faceNumber P 1 + 2 ^ P.dim := by sorry

/-- Theorem 1 with the exact bipartition imbalance term. -/
theorem IsCubical.strengthened_edge_bound (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 4 ≤ P.dim) (c : (polytopeGraph P).Coloring Bool) :
    ((P.dim : ℝ) + 1) / 2 * P.vertices.card - 2 ^ (P.dim - 1) +
      ((P.dim : ℝ) - 1) / 2 *
        |(Fintype.card (Black c) : ℝ) - Fintype.card (White c)| ≤ faceNumber P 1 := by sorry

/-- Bipartition follows from cubical convexity. -/
theorem IsCubical.bipartite (P : ConvexPolytope n) (hc : IsCubical P)
    (hdim : 3 ≤ P.dim) : (polytopeGraph P).Colorable 2 := by sorry

/-- Corollary 5, every proper-face dimension in the stated range. -/
theorem IsCubical.face_lower_bound (P : ConvexPolytope n)
    (hc : IsCubical P) (hdim : 3 ≤ P.dim) (i : ℕ)
    (hi : 1 ≤ i) (hid : i ≤ P.dim - 2) :
    ((P.dim.choose i : ℝ) + (P.dim - 1).choose (i - 1)) / 2 ^ i * P.vertices.card -
      2 ^ (P.dim - i) * (P.dim - 1).choose (i - 1) ≤ faceNumber P i := by sorry

/-- Corollary 5, the exact facet bound. -/
theorem IsCubical.facet_lower_bound (P : ConvexPolytope n)
    (hc : IsCubical P) (hdim : 3 ≤ P.dim) :
    ((P.dim : ℝ) - 1) / 2 ^ (P.dim - 2) * P.vertices.card -
      2 * ((P.dim : ℝ) - 2) ≤ faceNumber P (P.dim - 1) := by sorry

/-- The final strengthened proper-face formula. -/
theorem IsCubical.strengthened_face_lower_bound (P : ConvexPolytope n)
    (hc : IsCubical P) (hdim : 4 ≤ P.dim) (c : (polytopeGraph P).Coloring Bool)
    (i : ℕ) (hi : 1 ≤ i) (hid : i ≤ P.dim - 2) :
    ((P.dim.choose i : ℝ) + (P.dim - 1).choose (i - 1)) / 2 ^ i * P.vertices.card -
      2 ^ (P.dim - i) * (P.dim - 1).choose (i - 1) +
      ((P.dim : ℝ) - 1) * (P.dim - 1).choose (i - 1) / 2 ^ i *
        |(Fintype.card (Black c) : ℝ) - Fintype.card (White c)| ≤ faceNumber P i := by sorry

/-- The final strengthened facet formula. -/
theorem IsCubical.strengthened_facet_lower_bound (P : ConvexPolytope n)
    (hc : IsCubical P) (hdim : 4 ≤ P.dim) (c : (polytopeGraph P).Coloring Bool) :
    ((P.dim : ℝ) - 1) / 2 ^ (P.dim - 2) * P.vertices.card -
      2 * ((P.dim : ℝ) - 2) +
      ((P.dim : ℝ) - 1) * ((P.dim : ℝ) - 2) / 2 ^ (P.dim - 1) *
        |(Fintype.card (Black c) : ℝ) - Fintype.card (White c)| ≤
      faceNumber P (P.dim - 1) := by sorry

/-- The complete standard cube f-vector. -/
theorem standardCube_faceNumber (d : ℕ) (hd : 1 ≤ d) (i : ℕ) :
    faceNumber (standardCube d) i = 2 ^ (d - i) * d.choose i := by sorry

/-- The cube attains every proper-face bound. -/
theorem standardCube_face_equality (d : ℕ) (hd : 3 ≤ d) (i : ℕ)
    (hi : 1 ≤ i) (hid : i ≤ d - 2) :
    (d.choose i + (d - 1).choose (i - 1)) * (standardCube d).vertices.card =
      2 ^ i * faceNumber (standardCube d) i + 2 ^ d * (d - 1).choose (i - 1) := by sorry

/-- The cube attains the facet bound. -/
theorem standardCube_facet_equality (d : ℕ) (hd : 3 ≤ d) :
    (d - 1) * (standardCube d).vertices.card =
      2 ^ (d - 2) * faceNumber (standardCube d) (d - 1) +
        (d - 2) * 2 ^ (d - 1) := by sorry

/-- The lower, upper, and side layers of a facet-prism gluing. -/
inductive StackingLayer
  | lower | upper | side
  deriving DecidableEq
namespace StackingLayer
instance : PartialOrder StackingLayer where
  le a b := a = b ∨ b = side
  le_refl a := Or.inl rfl
  le_trans a b c hab hbc := by
    rcases hbc with rfl | rfl
    · exact hab
    · exact Or.inr rfl
  le_antisymm a b hab hba := by
    rcases hab with h | rfl
    · exact h
    · rcases hba with h | h
      · exact h.symm
      · exact h
end StackingLayer
/-- The retained/copy/side cells in a literal facet stacking. -/
def stackingCellValid (P : ConvexPolytope n) (F : FacetType P)
    (x : FaceType P × StackingLayer) : Prop :=
  match x.2 with
  | .lower => faceDim x.1.val < P.dim ∧ x.1 ≠ F.val
  | .upper => x.1 ≤ F.val
  | .side => x.1 < F.val
/-- The boundary cells in the gluing operation, with product incidence. -/
abbrev StackingCell (P : ConvexPolytope n) (F : FacetType P) :=
  {x : FaceType P × StackingLayer // stackingCellValid P F x}
/-- Adjoin the whole polytope above the glued boundary face poset. -/
abbrev StackingPoset (P : ConvexPolytope n) (F : FacetType P) :=
  WithTop (StackingCell P F)
/-- An actual polytope realizes the ordinary face poset of a facet stacking. -/
structure FacetStacking (P : ConvexPolytope n) (Q : ConvexPolytope m) where
  facet : FacetType P
  faceIso : FaceType Q ≃o StackingPoset P facet
/-- Finite realized facet stackings starting at a cube. -/
inductive IsStackedCubical : {n : ℕ} → ConvexPolytope n → Prop
  | cube {n d : ℕ} (P : ConvexPolytope n) (hd : 1 ≤ d)
      (h : CombinatoriallyEquivalent P (standardCube d)) : IsStackedCubical P
  | stack {n m : ℕ} {P : ConvexPolytope n} {Q : ConvexPolytope m}
      (hP : IsStackedCubical P) (S : FacetStacking P Q) : IsStackedCubical Q

/-- Every finite realized stacking sequence is cubical. -/
theorem IsStackedCubical.isCubical {P : ConvexPolytope n} (h : IsStackedCubical P) :
    3 ≤ P.dim → IsCubical P := by sorry

variable {P : ConvexPolytope n}

/-- Every finite realized stacking sequence attains the displayed bound. -/
theorem IsStackedCubical.edge_equality_real (hP : IsStackedCubical P)
    (hdim : 3 ≤ P.dim) :
    ((P.dim : ℝ) + 1) / 2 * P.vertices.card - 2 ^ (P.dim - 1) = faceNumber P 1 := by sorry

/-- Every finite realized stacking sequence attains the displayed bound. -/
theorem IsStackedCubical.face_equality_real (hP : IsStackedCubical P)
    (hdim : 3 ≤ P.dim) (i : ℕ) (hi : 1 ≤ i) (hid : i ≤ P.dim - 2) :
    ((P.dim.choose i : ℝ) + (P.dim - 1).choose (i - 1)) / 2 ^ i * P.vertices.card -
      2 ^ (P.dim - i) * (P.dim - 1).choose (i - 1) = faceNumber P i := by sorry

/-- Every finite realized stacking sequence attains the displayed bound. -/
theorem IsStackedCubical.facet_equality_real (hP : IsStackedCubical P)
    (hdim : 3 ≤ P.dim) :
    ((P.dim : ℝ) - 1) / 2 ^ (P.dim - 2) * P.vertices.card -
      2 * ((P.dim : ℝ) - 2) = faceNumber P (P.dim - 1) := by sorry

end LeanEval.Geometry.PlatonicClassification

namespace Convexity.StdSimplex
/-- The ordinary simplex in barycentric coordinates: nonnegative entries summing to one. -/
def coordinateSet (R I : Type*) [Semiring R] [PartialOrder R] [Fintype I] : Set (I → R) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}
end Convexity.StdSimplex

namespace DifferentialGeometry.Topology.PiecewiseLinear
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
/-- A compact intersection of finitely many closed affine halfspaces. -/
def IsHPolytope (C : Set E) : Prop :=
  IsCompact C ∧ ∃ (ι : Type) (_ : Finite ι) (l : ι → E →ₗ[ℝ] ℝ) (c : ι → ℝ),
    C = {x | ∀ i, l i x ≤ c i}
/-- Near x within s, the function agrees with affine maps on a finite polyhedral cover. -/
def IsPiecewiseAffineWithinAt (f : E → F) (s : Set E) (x : E) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (C : ι → Set E) (A : ι → E →ᵃ[ℝ] F),
    (∀ i, IsHPolytope (C i) ∧ C i ⊆ s ∧ EqOn f (A i) (C i)) ∧ (⋃ i, C i) ∈ 𝓝[s] x
/-- A function is piecewise affine locally at every point of its domain. -/
def IsPiecewiseAffineOn (f : E → F) (s : Set E) : Prop :=
  ∀ x ∈ s, IsPiecewiseAffineWithinAt f s x
/-- A bijection whose forward and inverse maps are piecewise affine. -/
def IsPLHomeomorphOn (f : E → F) (P : Set E) (Q : Set F) : Prop :=
  BijOn f P Q ∧ IsPiecewiseAffineOn f P ∧ IsPiecewiseAffineOn (Function.invFunOn f P) Q
/-- The ordinary boundary of the standard simplex in barycentric coordinates. -/
def stdSimplexBoundary (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {x | x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 1)) ∧ ∃ i, x i = 0}
/-- A set is a PL n-sphere through an actual piecewise affine homeomorphism. -/
def IsPLSphere (n : ℕ) (P : Set E) : Prop :=
  ∃ f : (Fin (n + 2) → ℝ) → E, IsPLHomeomorphOn f (stdSimplexBoundary (n + 1)) P
end DifferentialGeometry.Topology.PiecewiseLinear

namespace DifferentialGeometry.Topology.Engulfing
open Geometry
/-- The canonical barycentric-coordinate realization of a finite abstract simplicial complex. -/
def standardRealization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PreAbstractSimplicialComplex ι) : SimplicialComplex ℝ (ι → ℝ) := by
  classical
  apply SimplicialComplex.ofAffineIndependent (P.map (fun i => Pi.single i (1 : ℝ)))
  sorry
end DifferentialGeometry.Topology.Engulfing

namespace Cubical.Cube
/-- Bit-vector vertices of the standard n-cube. -/
abbrev Vertex (n : ℕ) := Fin n → Bool
/-- Coordinate subface through s with the specified free coordinates. -/
def FaceAt {n : ℕ} (s : Vertex n) (A : Finset (Fin n)) : Set (Vertex n) :=
  {t | ∀ i, i ∉ A → t i = s i}
end Cubical.Cube
namespace Cubical.PL
/-- A coordinate subface, as its actual vertex set. -/
def coordinateFace {n : ℕ} (s : Cube.Vertex n) (A : Finset (Fin n)) :
    Finset (Cube.Vertex n) :=
  Finset.univ.filter (fun t => t ∈ Cube.FaceAt s A)
/-- Transport the coordinate subface along a cell chart. -/
def chartFace {V : Type*} [DecidableEq V] {F : Finset V} {n : ℕ}
    (φ : Cube.Vertex n ≃ F) (s : Cube.Vertex n) (A : Finset (Fin n)) : Finset V :=
  (coordinateFace s A).image (fun t => (φ t).val)
/-- A finite cubical complex whose cells have genuine cube charts, all coordinate
subfaces are present, and every nonempty intersection is a common face. -/
structure CubeComplex (V : Type*) [Fintype V] [DecidableEq V] where
  faces : Finset (Finset V)
  nonempty : ∀ F ∈ faces, F.Nonempty
  singleton_mem : ∀ v, {v} ∈ faces
  inter_mem : ∀ F ∈ faces, ∀ G ∈ faces, (F ∩ G).Nonempty → F ∩ G ∈ faces
  dimension : Finset V → ℕ
  chart : ∀ F ∈ faces, Cube.Vertex (dimension F) ≃ F
  chart_faces : ∀ F (hF : F ∈ faces) s A,
    chartFace (chart F hF) s A ∈ faces ∧
      dimension (chartFace (chart F hF) s A) = A.card
  subfaces : ∀ F (hF : F ∈ faces) G, G ∈ faces → G ⊆ F →
    ∃ s A, G = chartFace (chart F hF) s A
namespace CubeComplex
open Geometry Cubical.Bipartite
open DifferentialGeometry.Topology.Engulfing
open DifferentialGeometry.Topology.PiecewiseLinear
variable {V : Type*} [Fintype V] [DecidableEq V] (K : CubeComplex V)
/-- The actual cells of the complex. -/
abbrev Cell := {F : Finset V // F ∈ K.faces}
instance : Fintype K.Cell := inferInstance
/-- The graph of actual one-dimensional cells. -/
def graph : SimpleGraph V where
  Adj v w := v ≠ w ∧ {v, w} ∈ K.faces ∧ K.dimension {v, w} = 1
  symm := by sorry
  loopless := by sorry
/-- The simplicial complex of nonempty chains of cells. -/
def orderComplex : PreAbstractSimplicialComplex K.Cell where
  faces := {C | C.Nonempty ∧ ∀ F ∈ C, ∀ G ∈ C, F ≤ G ∨ G ≤ F}
  isRelLowerSet_faces := by sorry
/-- Canonical geometric realization of the face-chain complex. -/
def realization := standardRealization K.orderComplex
/-- This exact face-chain realization is genuinely PL homeomorphic to a sphere. -/
def IsSphere (m : ℕ) : Prop := IsPLSphere m K.realization.space
/-- Count the actual i-dimensional cells without multiplicity. -/
def faceNumber (i : ℕ) : ℕ := Fintype.card {F : K.Cell // K.dimension F.val = i}

/-- Corollary 4 for every finite cubical PL sphere in the stated range. -/
theorem cubical_pl_lower_bound (d : ℕ) (hd : 4 ≤ d) (hK : K.IsSphere (d - 1)) :
    Nonempty (K.graph.Coloring Bool) ∧
    ∀ c : K.graph.Coloring Bool,
      ((d : ℝ) + 1) / 2 * K.faceNumber 0 - 2 ^ (d - 1) +
        ((d : ℝ) - 1) / 2 *
          |(Fintype.card (Black c) : ℝ) - Fintype.card (White c)| ≤ K.faceNumber 1 := by sorry

end CubeComplex
end Cubical.PL
