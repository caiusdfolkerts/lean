module
public import Mathlib
public import cubical_indecomposability
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
/-!
# A counterexample to Smilansky's conjecture

The principal result is an actual rational convex four-polytope whose facets
are combinatorial cubes, whose f-vector is (144,404,390,130), and whose parallel
redrawings are homotheties. Its arbitrary convex Minkowski summands have the
strong customary homothety property. The supporting deformation-space criterion
and the complete auxiliary 32-vertex block are included below.

All custom mathematical data and predicates are independently copied with
exact original names and semantics. Only proofs of well-formedness are left
as Challenge holes. In particular, no rigidity or numerical conclusion is
built into the polytope, cubicality, redrawing or block definitions. Geometric
infrastructure adapted from Daniele Cappello is attributed in the preserved
original source headers and third-party Apache-2.0 licences.
-/
@[expose] public section
noncomputable section
open Set
open scoped Pointwise Classical
namespace PalomarCubical.Geometry

/-- Euclidean n-space, with Mathlib's usual real inner product. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A nonempty finite convex hull, listed by exactly its extreme vertices. -/
structure ConvexPolytope (n : ℕ) where
  vertices : Finset (E n)
  vertices_nonempty : vertices.Nonempty
  vertices_eq_extremePoints :
    (vertices : Set (E n)) =
      Set.extremePoints ℝ (convexHull ℝ ((vertices : Set (E n))))

private def toSource {n : ℕ} (P : ConvexPolytope n) :
    LeanEval.Geometry.PlatonicClassification.ConvexPolytope n :=
  ⟨P.vertices,P.vertices_nonempty,P.vertices_eq_extremePoints⟩
private def ofSource {n : ℕ} (P : LeanEval.Geometry.PlatonicClassification.ConvexPolytope n) :
    ConvexPolytope n := ⟨P.vertices,P.vertices_nonempty,P.vertices_eq_extremePoints⟩
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
end PalomarCubical.Geometry


namespace PalomarCubical.Geometry
open ConvexPolytope
variable {n : ℕ}
/-- Affine dimension of a geometric face. -/
noncomputable def ConvexPolytope.faceDim {n : ℕ} (F : Set (E n)) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ F)
/-- Every actual finite convex polytope has only finitely many exposed faces. -/
theorem finite_isFace (P : ConvexPolytope n) :
    Set.Finite {F : Set (E n) | P.IsFace F} := by
  exact LeanEval.Geometry.PlatonicClassification.finite_isFace (toSource P)
/-- All nonempty geometric faces. -/
noncomputable def faceSet (P : ConvexPolytope n) : Finset (Set (E n)) :=
  (finite_isFace P).toFinset
/-- The literal number of geometric faces of affine dimension i. -/
noncomputable def faceNumber (P : ConvexPolytope n) (i : ℕ) : ℕ := by
  classical
  exact ((faceSet P).filter (fun F => faceDim F = i)).card
theorem facePolytope_vertices_nonempty (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) : (P.vertices.filter (· ∈ f)).Nonempty := by
  exact (LeanEval.Geometry.PlatonicClassification.facePolytope (toSource P) hf).vertices_nonempty
theorem facePolytope_vertices_extreme (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) : ((P.vertices.filter (· ∈ f) : Finset (E n)) : Set (E n)) =
      Set.extremePoints ℝ (convexHull ℝ ((P.vertices.filter (· ∈ f) : Finset (E n)) : Set (E n))) := by
  exact (LeanEval.Geometry.PlatonicClassification.facePolytope (toSource P) hf).vertices_eq_extremePoints
/-- The actual face hull, with precisely the original extreme vertices on it. -/
noncomputable def facePolytope (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) : ConvexPolytope n where
  vertices := P.vertices.filter (· ∈ f)
  vertices_nonempty := facePolytope_vertices_nonempty P hf
  vertices_eq_extremePoints := facePolytope_vertices_extreme P hf
/-- A sign vector of the standard geometric cube. -/
noncomputable def vertIper {d : ℕ} (s : Fin d → Bool) : E d :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => if s i then 1 else -1)
/-- The set of all 2^d cube vertices. -/
noncomputable def verticiIper (d : ℕ) : Finset (E d) :=
  (Finset.univ : Finset (Fin d → Bool)).image vertIper
theorem cube_vertices_nonempty (d : ℕ) : (verticiIper d).Nonempty := by
  exact LeanEval.Geometry.PlatonicClassification.verticiIper_nonempty d
theorem cube_vertices_extreme (d : ℕ) : (verticiIper d : Set (E d)) =
    Set.extremePoints ℝ (convexHull ℝ (verticiIper d : Set (E d))) := by
  exact LeanEval.Geometry.PlatonicClassification.verticiIper_eq_extremePoints d
/-- The complete standard sign-vector hull in every dimension, including zero. -/
noncomputable def standardCube (d : ℕ) : ConvexPolytope d :=
  ⟨verticiIper d, cube_vertices_nonempty d, cube_vertices_extreme d⟩
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
end PalomarCubical.Geometry

namespace PalomarCubical.Polytopes
open PalomarCubical.Geometry
open PalomarCubical.Geometry.ConvexPolytope
variable {d : ℕ}
/-- Positive homothety of actual convex sets, allowing translation. -/
def IsHomotheticCopy (P A : ConvexPolytope d) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ b : E d,
    A.toSet = (fun x : E d => r • x + b) '' P.toSet
/-- Nontrivial Minkowski decomposability, allowing summands of any dimension. -/
def MinkowskiDecomposable (P : ConvexPolytope d) : Prop :=
  ∃ A B : ConvexPolytope d,
    P.toSet = A.toSet + B.toSet ∧
    ¬IsHomotheticCopy P A ∧ ¬IsHomotheticCopy P B
/-- Every extreme vertex has rational coordinates. -/
def RationalCoordinates (P : ConvexPolytope d) : Prop :=
  ∀ v ∈ P.vertices, ∀ i : Fin d, ∃ q : ℚ, (q : ℝ) = v i
/-- Arbitrary real edge scalars, with parallelism on every actual geometric edge. -/
def IsParallelMap (P : ConvexPolytope d) (f : E d → E d) : Prop :=
  ∀ x ∈ P.vertices, ∀ y ∈ P.vertices, GeneralVertexStep P x y →
    ∃ c : ℝ, f y - f x = c • (y - x)
/-- One uniform scaling and one translation at all extreme vertices. -/
def IsHomothetyOnVertices (P : ConvexPolytope d) (f : E d → E d) : Prop :=
  ∃ a : ℝ, ∃ b : E d, ∀ v ∈ P.vertices, f v = a • v + b
/-- Actual extreme vertices, with no extraneous ambient points. -/
abbrev Vertex (P : ConvexPolytope d) := {x : E d // x ∈ P.vertices}
def ParallelAssignment (P : ConvexPolytope d) (h : Vertex P → E d) : Prop :=
  ∀ u v : Vertex P, GeneralVertexStep P u v →
    ∃ a : ℝ, h v - h u = a • ((v : E d) - (u : E d))
theorem parallelAssignment_zero (P : ConvexPolytope d) : ParallelAssignment P 0 := by
  exact (Papers.Polytopes.redrawingSpace (toSource P)).zero_mem
theorem parallelAssignment_add (P : ConvexPolytope d) :
    ∀ {h k : Vertex P → E d}, ParallelAssignment P h → ParallelAssignment P k →
      ParallelAssignment P (h+k) := by
  exact (Papers.Polytopes.redrawingSpace (toSource P)).add_mem
theorem parallelAssignment_smul (P : ConvexPolytope d) :
    ∀ (a : ℝ) {h : Vertex P → E d}, ParallelAssignment P h → ParallelAssignment P (a • h) := by
  exact (Papers.Polytopes.redrawingSpace (toSource P)).smul_mem
/-- The literal actual-edge parallel assignment subspace. -/
def redrawingSpace (P : ConvexPolytope d) : Submodule ℝ (Vertex P → E d) where
  carrier := {h | ParallelAssignment P h}
  zero_mem' := parallelAssignment_zero P
  add_mem' := parallelAssignment_add P
  smul_mem' := parallelAssignment_smul P
theorem translation_parallel (P : ConvexPolytope d) (b : E d) :
    ParallelAssignment P (fun _ => b) := by
  exact (Papers.Polytopes.translationMap (toSource P) b).2
/-- The linear map taking a translation vector to its constant assignment. -/
def translationMap (P : ConvexPolytope d) : E d →ₗ[ℝ] redrawingSpace P where
  toFun b := ⟨fun _ => b, translation_parallel P b⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- The subspace of constant translations. -/
def translationSpace (P : ConvexPolytope d) : Submodule ℝ (redrawingSpace P) :=
  (translationMap P).range
instance (P : ConvexPolytope d) :
    CoeFun (redrawingSpace P) (fun _ => Vertex P → E d) := ⟨Subtype.val⟩
/-- The deformation space is exactly parallel assignments modulo translations. -/
abbrev DeformationSpace (P : ConvexPolytope d) :=
  redrawingSpace P ⧸ translationSpace P
/-- Dimension of the actual quotient space D(P). -/
def deformationDimension (P : ConvexPolytope d) : ℕ :=
  Module.finrank ℝ (DeformationSpace P)
variable (P : ConvexPolytope d) {F : Set (E d)} (hF : P.IsFace F)
/-- Inclusion of an actual extreme vertex of a face into the original vertex set. -/
def faceVertex (v : Vertex (facePolytope P hF)) : Vertex P :=
  ⟨v, (Finset.mem_filter.mp v.property).1⟩
theorem redrawing_restriction_parallel (h : redrawingSpace P) :
    ParallelAssignment (facePolytope P hF) (fun v => h (faceVertex P hF v)) := by
  exact (Papers.Polytopes.redrawingRestriction (toSource P) hF h).2
/-- Restriction of actual parallel assignments to a face. -/
def redrawingRestriction : redrawingSpace P →ₗ[ℝ] redrawingSpace (facePolytope P hF) where
  toFun h := ⟨fun v => h (faceVertex P hF v), redrawing_restriction_parallel P hF h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem redrawing_restriction_translation : ∀ h, h ∈ translationSpace P →
    redrawingRestriction P hF h ∈ translationSpace (facePolytope P hF) := by
  rintro h ⟨b,rfl⟩
  exact ⟨b,rfl⟩
/-- The induced map on literal parallel redrawings modulo translations. -/
def deformationRestriction : DeformationSpace P →ₗ[ℝ] DeformationSpace (facePolytope P hF) :=
  (translationSpace P).mapQ (translationSpace (facePolytope P hF))
    (redrawingRestriction P hF) (redrawing_restriction_translation P hF)
/-- A face determines P exactly when quotient-space restriction is injective. -/
def FaceDetermines : Prop := Function.Injective (deformationRestriction P hF)
/-- Lemma 3(ii) for vertex assignments. -/
theorem redrawing_zero_of_two_neighbors {P : ConvexPolytope d}
    (h : redrawingSpace P) {x y z : Vertex P}
    (hxy : GeneralVertexStep P x y) (hxz : GeneralVertexStep P x z)
    (hyz : y ≠ z) (hy : h y = 0) (hz : h z = 0) : h x = 0 := by
  exact Papers.Polytopes.redrawing_zero_of_two_neighbors h hxy hxz hyz hy hz
/-- An invertible homogeneous representative of a projectivity. -/
abbrev HomogeneousProjectivity (d : ℕ) := E (d + 1) ≃ₗ[ℝ] E (d + 1)
/-- Append homogeneous coordinate one. -/
def homogeneousPoint {d : ℕ} (x : E d) : E (d + 1) :=
  WithLp.toLp 2 (Fin.lastCases 1 (fun i => x i))
/-- The actual denominator in the chosen affine chart. -/
def projectiveDenominator {d : ℕ} (T : HomogeneousProjectivity d) (x : E d) : ℝ :=
  T (homogeneousPoint x) (Fin.last d)
/-- Usual affine-chart action of an invertible homogeneous map. -/
def projectiveApply {d : ℕ} (T : HomogeneousProjectivity d) (x : E d) : E d :=
  WithLp.toLp 2 (fun i =>
    T (homogeneousPoint x) i.castSucc / projectiveDenominator T x)
/-- Positivity of the denominator on every point of the specified set. -/
def ProjectivelyPositiveOn {d : ℕ} (T : HomogeneousProjectivity d) (S : Set (E d)) : Prop :=
  ∀ x ∈ S, 0 < projectiveDenominator T x
/-- One positive projectivity makes the two interfaces affinely equivalent,
fixing their common face pointwise. -/
def HasAffineInterfaceNormalization (P : ConvexPolytope 4)
    (F H Q : Set (E 4)) : Prop :=
  ∃ T : HomogeneousProjectivity 4, ProjectivelyPositiveOn T P.toSet ∧
    ∃ e : E 4 ≃ᵃ[ℝ] E 4,
      e '' (projectiveApply T '' F) = projectiveApply T '' H ∧
      ∀ x ∈ projectiveApply T '' Q, e x = x
/-- A nondegenerate affine three-cube after a positive projectivity. -/
def ProjectivelyParallelepiped (G : Set (E 4)) : Prop :=
  ∃ T : HomogeneousProjectivity 4, ProjectivelyPositiveOn T G ∧
    ∃ e : E 3 →ᵃ[ℝ] E 4, Function.Injective e ∧
      projectiveApply T '' G = e '' (standardCube 3).toSet
end PalomarCubical.Polytopes

namespace PalomarCubical.Results
open PalomarCubical.Geometry
open PalomarCubical.Geometry.ConvexPolytope PalomarCubical.Polytopes
/-- Theorem 1 in full, including arbitrary convex summands. -/
theorem theorem_one :
    ∃ K : ConvexPolytope 4,
      K.IsFullDim ∧ RationalCoordinates K ∧ ¬MinkowskiDecomposable K ∧ IsCubical K ∧
      faceNumber K 0 = 144 ∧ faceNumber K 1 = 404 ∧
      faceNumber K 2 = 390 ∧ faceNumber K 3 = 130 ∧
      (∀ f : E 4 → E 4, IsParallelMap K f → IsHomothetyOnVertices K f) ∧
      (∀ A B : Set (E 4), Convex ℝ A → Convex ℝ B → K.toSet = A + B →
        ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ ∃ b : E 4,
          A = (fun x : E 4 => r • x + b) '' K.toSet ∧
          B = (fun x : E 4 => (1 - r) • x - b) '' K.toSet) := by
  obtain ⟨K,hfull,hrat,hind,hcub,h0,h1,h2,h3,hred,hsum⟩ := CubicalIndecomposability.theorem_one
  refine ⟨ofSource K,hfull,hrat,?_,hcub,h0,h1,h2,h3,hred,hsum⟩
  rintro ⟨A,B,hAB,hA,hB⟩
  apply hind
  exact ⟨toSource A,toSource B,hAB,(fun h => hA h),(fun h => hB h)⟩
/-- Lemma 2: the literal one-dimensional quotient criterion for convex summands. -/
theorem lemma_two {d : ℕ} (P : ConvexPolytope d)
    (hD : deformationDimension P = 1)
    (A B : Set (E d)) (hA : Convex ℝ A) (hB : Convex ℝ B)
    (hP : P.toSet = A + B) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ ∃ b : E d,
      A = (fun x : E d => r • x + b) '' P.toSet ∧
      B = (fun x : E d => (1 - r) • x - b) '' P.toSet := by
  exact CubicalIndecomposability.lemma_two (toSource P) hD A B hA hB hP
/-- Lemma 3(i): affinely independent four-cycles have only homothetic redrawings. -/
theorem lemma_three_one {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p h : Fin 4 → V) (hp : AffineIndependent ℝ p)
    (hparallel : ∀ i : Fin 4, ∃ a : ℝ,
      h (i + 1) - h i = a • (p (i + 1) - p i)) :
    ∃ a : ℝ, ∃ b : V, ∀ i : Fin 4, h i = a • p i + b := by
  exact CubicalIndecomposability.lemma_three_one p h hp hparallel
end PalomarCubical.Results

namespace PalomarCubical.Results.Block
open PalomarCubical.Geometry
open PalomarCubical.Geometry.ConvexPolytope PalomarCubical.Polytopes
/-- Proposition 5, including genuine quotient restriction and geometric interfaces. -/
theorem proposition_five :
    ∃ P : ConvexPolytope 4,
      P.IsFullDim ∧ RationalCoordinates P ∧ IsCubical P ∧
      faceNumber P 0 = 32 ∧ faceNumber P 1 = 80 ∧
      faceNumber P 2 = 72 ∧ faceNumber P 3 = 24 ∧
      ∃ F H G Q : Set (E 4),
      ∃ hF : P.IsFace F, ∃ hH : P.IsFace H, ∃ hG : P.IsFace G,
      ∃ hQ : P.IsFace Q,
        faceDim F = 3 ∧ faceDim H = 3 ∧ faceDim G = 3 ∧
        F ∩ H = Q ∧ faceDim Q = 2 ∧
        (facePolytope P hQ).vertices.card = 4 ∧
        Disjoint G (F ∪ H) ∧
        FaceDetermines P hH ∧ FaceDetermines P hG ∧
        Module.finrank ℝ (deformationRestriction P hF).range ≤ 2 ∧
        HasAffineInterfaceNormalization P F H Q ∧
        ProjectivelyParallelepiped G := by
  obtain ⟨P,hP⟩ := CubicalIndecomposability.Block.proposition_five
  exact ⟨ofSource P,hP⟩
end PalomarCubical.Results.Block
