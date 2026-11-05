import cubical.polytope.face_order
import cubical.polytope.ipercubo

/-!
# Geometric meaning of “cubical”

The standard cube is the convex hull of all sign vectors. A polytope is
cubical when each facet has the ordinary nonempty face poset of a cube.
No lower bound, bipartition, connectivity, or rigidity claim enters this
definition. Rank preservation follows from `faceOrderIso_dimension`.
-/

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- The standard geometric cube in every dimension, including dimension zero. -/
noncomputable def standardCube (d : ℕ) : ConvexPolytope d :=
  ⟨verticiIper d, verticiIper_nonempty d, verticiIper_eq_extremePoints d⟩

@[simp] theorem standardCube_vertices_card (d : ℕ) :
    (standardCube d).vertices.card = 2 ^ d := card_verticiIper d

theorem standardCube_eq_ipercubo (d : ℕ) (hd : 1 ≤ d) :
    standardCube d = ipercubo d hd := rfl

/-- Combinatorial equivalence of finite convex polytopes. -/
def CombinatoriallyEquivalent {n m : ℕ}
    (P : ConvexPolytope n) (Q : ConvexPolytope m) : Prop :=
  Nonempty (FaceType P ≃o FaceType Q)

/-- Every geometric facet is combinatorially a cube of the required dimension. -/
def IsCubical {n : ℕ} (P : ConvexPolytope n) : Prop :=
  ∀ (F : Set (E n)) (hF : P.IsFace F),
    faceDim F + 1 = P.dim →
    CombinatoriallyEquivalent (facePolytope P hF) (standardCube (P.dim - 1))

/-- Each two-dimensional face has exactly four extreme vertices. -/
def HasQuadrilateralTwoFaces {n : ℕ} (P : ConvexPolytope n) : Prop :=
  ∀ (F : Set (E n)) (hF : P.IsFace F), faceDim F = 2 →
    (facePolytope P hF).vertices.card = 4

end LeanEval.Geometry.PlatonicClassification
