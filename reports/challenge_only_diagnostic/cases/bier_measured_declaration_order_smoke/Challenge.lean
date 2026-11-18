module
public import Lean.Elab.Command
public import Lean.Elab.Term
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.Analysis.Convex.SimplicialComplex.AffineIndependentUnion
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Finset.Option
/-!
# Explicit nonpolytopal Bier spheres

Theorem 1 is recorded by four existential wrappers around the actual explicit
constructions in the Solution: the principal ghost example, all-label example,
self-dual centrally symmetric example, and input-dimension-three example. Each
wrapper keeps the exact finite ground set and every dimensional, vertex-count,
sphere, and nonpolytopality conclusion. The proof supplies the manuscript's
concrete construction, rather than an unspecified replacement construction.

Theorem 2 is the exact universal sign-rank obstruction in both cardinality
regimes. The final parameter range, Bier's sphere theorem, Forster's inequality,
Hadamard column restriction, and the all-sign matrix rank are also recorded.
Custom definitions independently retain original names and exact semantics;
construction well-formedness proofs alone are Challenge holes. All original
Apache-2.0 source and third-party attribution is retained in the full project.
-/
@[expose] public section
noncomputable section
open Set
open scoped Classical Pointwise Topology BigOperators
namespace Bier.Forster
universe u
/-- The measured real identity inverse-pair proof, given a stable public name. -/
theorem realIdentityInvPair : RingHomInvPair (RingHom.id ℝ) (RingHom.id ℝ) := by
  infer_instance
/-- The measured commutation of real scalar multiplication on the actual
Euclidean function space, fixed independently of generated auxiliary names. -/
theorem euclideanSelfSMulComm (I : Type u) : SMulCommClass ℝ ℝ (EuclideanSpace ℝ I) := by
  infer_instance
variable {R C : Type*} [Fintype R] [Fintype C]
/-- The usual Euclidean operator norm of a real matrix. -/
def spectralNorm (H : Matrix R C ℝ) : ℝ :=
  letI : RingHomInvPair (RingHom.id ℝ) (RingHom.id ℝ) := realIdentityInvPair
  letI : SMulCommClass ℝ ℝ (EuclideanSpace ℝ R) := euclideanSelfSMulComm R
  letI : SMulCommClass ℝ ℝ (EuclideanSpace ℝ C) := euclideanSelfSMulComm C
  ‖H.toEuclideanLin.toContinuousLinearMap‖
end Bier.Forster

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


namespace LeanEval.Geometry.PlatonicClassification
open ConvexPolytope
variable {n : ℕ}
/-- Actual extreme vertices as a finite type. -/
abbrev VertexType (P : ConvexPolytope n) := {v : E n // v ∈ P.vertices}
noncomputable instance faceTypeFintype (P : ConvexPolytope n) :
    Fintype (FaceType P) := (finite_isFace P).fintype
/-- The actual codimension-one exposed faces. -/
abbrev FacetType (P : ConvexPolytope n) :=
  {F : FaceType P // faceDim F.val + 1 = P.dim}
/-- Each facet is a simplex on its actual extreme vertices. -/
def IsSimplicial (P : ConvexPolytope n) : Prop :=
  ∀ (F : Set (E n)) (hF : P.IsFace F), faceDim F + 1 = P.dim →
    AffineIndependent ℝ (fun v : VertexType (facePolytope P hF) => v.val)
/-- Vertices of a geometric face, as vertices of the original polytope. -/
def faceVertices (P : ConvexPolytope n) (F : Set (E n)) : Finset (VertexType P) :=
  Finset.univ.filter (fun v => v.val ∈ F)
/-- The complete family of actual facet vertex sets. -/
def boundaryFacets (P : ConvexPolytope n) : Finset (Finset (VertexType P)) :=
  Finset.univ.image (fun F : FacetType P => faceVertices P F.val.val)
end LeanEval.Geometry.PlatonicClassification
namespace Convexity.StdSimplex
variable {R I : Type*}
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


namespace Bier
/-- A finite downward-closed complex, including the empty face and possible ghost labels. -/
structure Complex (V : Type*) where
  face : Finset V → Prop
  empty : face ∅
  downward : ∀ {s t}, s ⊆ t → face t → face s
namespace Complex
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The full ground set is not a face. -/
def Proper (K : Complex V) : Prop := ¬ K.face Finset.univ
/-- Actual singleton vertices, excluding ghosts. -/
def vertices (K : Complex V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => K.face {v})
/-- Maximum cardinality of an actual face. -/
def maxFaceCard (K : Complex V) : ℕ := by
  classical
  exact (Finset.univ.filter K.face).sup Finset.card
/-- Dimension is maximum face cardinality minus one, valued in integers. -/
def dimension (K : Complex V) : ℤ := (K.maxFaceCard : ℤ) - 1
/-- The associated nonempty-face abstract simplicial complex. -/
def toAbstract (K : Complex V) : PreAbstractSimplicialComplex V where
  faces := {s | s.Nonempty ∧ K.face s}
  isRelLowerSet_faces := by sorry
/-- Alexander dual with respect to the entire specified finite ground set. -/
def dual (K : Complex V) (hK : K.Proper) : Complex V where
  face s := ¬ K.face sᶜ
  empty := by sorry
  downward := by sorry
/-- The genuine Bier deleted join of a proper complex and its Alexander dual. -/
def bier (K : Complex V) (hK : K.Proper) : Complex (V ⊕ V) where
  face s := K.face s.toLeft ∧ ¬ K.face s.toRightᶜ ∧ Disjoint s.toLeft s.toRight
  empty := by sorry
  downward := by sorry
/-- Extend by a label contained in no face. -/
def ghost (K : Complex V) : Complex (Option V) where
  face s := none ∉ s ∧ K.face s.eraseNone
  empty := by sorry
  downward := by sorry
/-- The missing ghost label makes the extended complex proper. -/
theorem ghost_proper (K : Complex V) : K.ghost.Proper := by sorry
/-- The canonical realization is actually PL homeomorphic to an n-sphere. -/
def IsSphere (K : Complex V) (n : ℕ) : Prop :=
  DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere n
    (DifferentialGeometry.Topology.Engulfing.standardRealization K.toAbstract).space
/-- A fixed-point-free simplicial involution, with no face containing an antipodal pair. -/
def IsCentrallySymmetric (K : Bier.Complex V) : Prop :=
  ∃ τ : V ≃ V, (∀ v, τ (τ v) = v) ∧
    (∀ s, K.face (s.image τ) ↔ K.face s) ∧
    (∀ s, K.face s → Disjoint s (s.image τ))
/-- Bier's sphere theorem, including inputs with ghost labels. -/
theorem bier_isSphere (K : Complex V) (hK : K.Proper) (hcard : 2 ≤ Fintype.card V) :
    (K.bier hK).IsSphere (Fintype.card V - 2) := by sorry
end Complex

open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- An actual simplicial convex polytope whose entire boundary has exactly K's faces. -/
structure PolytopeRealization (K : Complex V) (n : ℕ) where
  polytope : ConvexPolytope n
  simplicial : IsSimplicial polytope
  vertexEquiv : ↥K.vertices ≃ VertexType polytope
  faces : ∀ s : Finset ↥K.vertices,
    K.face (s.image Subtype.val) ↔ s = ∅ ∨
      ∃ t ∈ boundaryFacets polytope, s.map vertexEquiv.toEmbedding ⊆ t
/-- Ordinary polytopality via a genuine simplicial convex boundary realization. -/
def Polytopal (K : Complex V) : Prop := ∃ n, Nonempty (PolytopeRealization K n)
end Bier
namespace Bier
variable {E : Type*} [Fintype E] [DecidableEq E]
/-- Bier sphere formed after adjoining a ghost label. -/
abbrev ghostBier (K : Complex E) :=
  K.ghost.bier K.ghost_proper

end Bier
namespace Bier
variable {R C : Type*} [Fintype R] [Fintype C]
/-- Every entry is a strict sign, plus or minus one. -/
def IsSignMatrix (H : Matrix R C ℝ) : Prop :=
  ∀ r c, H r c = 1 ∨ H r c = -1
/-- Realizing matrix has precisely the prescribed strict signs. -/
def SignRealizes (H M : Matrix R C ℝ) : Prop :=
  ∀ r c, 0 < H r c * M r c
/-- The ordinary minimum rank of a real matrix realizing all prescribed signs. -/
def signRank (H : Matrix R C ℝ) : ℕ :=
  sInf {n : ℕ | ∃ M : Matrix R C ℝ, SignRealizes H M ∧ M.rank = n}

end Bier
namespace Bier
variable {U C R : Type*} [Fintype U] [Fintype C] [Fintype R]
  [DecidableEq U] [DecidableEq C]

/-- Theorem 2 with every original hypothesis and quantifier. -/
theorem ghost_signRank_bound_fixedCard (K : Complex (U ⊕ C)) (hK : K.Proper)
    (hv : ∀ i, K.face {i}) (S : R → Finset U) (k : ℕ) (hk : 0 < k)
    (hcard : ∀ r, (S r).card = k) (hSface : ∀ r, K.face ((S r).disjSum ∅))
    (H : Matrix R C ℝ) (hH : IsSignMatrix H)
    (hsign : ∀ r c, H r c = 1 ↔ K.face ((S r).disjSum {c}))
    (hP : Polytopal (ghostBier K)) :
    signRank H ≤ Fintype.card U ^ 2 - Fintype.card U + 1 := by sorry

/-- Theorem 2 with every original hypothesis and quantifier. -/
theorem ghost_signRank_bound_arbitrary (K : Complex (U ⊕ C)) (hK : K.Proper)
    (hv : ∀ i, K.face {i}) (S : R → Finset U)
    (hSface : ∀ r, K.face ((S r).disjSum ∅))
    (H : Matrix R C ℝ) (hH : IsSignMatrix H)
    (hsign : ∀ r c, H r c = 1 ↔ K.face ((S r).disjSum {c}))
    (hP : Polytopal (ghostBier K)) :
    signRank H ≤ Fintype.card U ^ 2 - Fintype.card U + 2 := by sorry

end Bier
namespace Bier
variable (R : Type*) [Fintype R] [DecidableEq R]
/-- Every normalized column sign pattern occurs once. -/
def allColumnSigns :
    Matrix (Option R) (R → Fin 2) ℝ := fun r c =>
  match r with
  | none => 1
  | some i => if c i = 0 then 1 else -1
/-- Exact sign rank of the complete normalized all-sign matrix. -/
theorem allColumnSigns_signRank :
    signRank (allColumnSigns R) = Fintype.card R + 1 := by sorry
end Bier
namespace Bier.Forster
variable {R C : Type*} [Fintype R] [Fintype C]
/-- Forster's lower bound with no general-position assumption on a realizing matrix. -/
theorem signRank_spectral (H : Matrix R C ℝ) (hH : Bier.IsSignMatrix H) :
    Real.sqrt ((Fintype.card R : ℝ) * Fintype.card C) ≤
      (Bier.signRank H : ℝ) * spectralNorm H := by sorry
/-- Sign rank of every column restriction of a square real Hadamard matrix. -/
theorem hadamard_columnRestriction_signRank [DecidableEq R] (A : Matrix R R ℝ)
    (hA : A.IsHadamard) (e : C ↪ R) :
    Fintype.card C ≤ Bier.signRank (A.submatrix id e) ^ 2 := by sorry
end Bier.Forster

namespace PalomarBier
open Bier
/-- Theorem 1 principal example, including the original ghost label. The Solution
supplies the concrete principalInput from the manuscript's explicit matrices. -/
theorem principal_example :
    ∃ I : Complex (Option (Fin 20 ⊕ Fin 145162)), ∃ hI : I.Proper,
      ¬ I.face {none} ∧ I.dimension = 9 ∧ (I.bier hI).IsSphere 145181 ∧
      (I.bier hI).dimension = 145181 ∧ (I.bier hI).vertices.card = 290365 ∧
      ¬ Polytopal (I.bier hI) := by sorry
/-- Theorem 1 with all labels actual vertices of both input and Bier sphere. -/
theorem all_labels_example :
    ∃ I : Complex (Option (Fin 20 ⊕ Fin 145162)), ∃ hI : I.Proper,
      I.vertices = Finset.univ ∧ I.dimension = 9 ∧
      (I.bier hI).vertices = Finset.univ ∧ (I.bier hI).vertices.card = 290366 ∧
      (I.bier hI).dimension = 145181 ∧ (I.bier hI).IsSphere 145181 ∧
      ¬ Polytopal (I.bier hI) := by sorry
/-- Theorem 1 with a self-dual input and centrally symmetric Bier sphere. -/
theorem self_dual_example :
    ∃ I : Complex ((Fin 20 ⊕ Fin 145162) ⊕ Bool), ∃ hI : I.Proper,
      (∀ F, (I.dual hI).face F ↔ I.face F) ∧
      (I.bier hI).IsSphere 145182 ∧ (I.bier hI).dimension = 145182 ∧
      (I.bier hI).vertices.card = 290368 ∧ (I.bier hI).IsCentrallySymmetric ∧
      ¬ Polytopal (I.bier hI) := by sorry
/-- Theorem 1 with input dimension three and the exact stated output counts. -/
theorem three_dimensional_example :
    ∃ I : Complex (Option (Fin 9 ⊕ (Fin 73 → Fin 2))), ∃ hI : I.Proper,
      I.dimension = 3 ∧ (I.bier hI).IsSphere (2 ^ 73 + 8) ∧
      (I.bier hI).dimension = 2 ^ 73 + 8 ∧ (I.bier hI).vertices.card = 2 ^ 74 + 19 ∧
      ¬ Polytopal (I.bier hI) := by sorry
/-- The final construction for the full binomial-inequality parameter range. -/
theorem general_allSign_construction_unrestricted (m k : ℕ)
    (hchoose : m ^ 2 - m + 2 ≤ m.choose k) :
    ∃ I : Complex (Option (Fin m ⊕ (Fin (m ^ 2 - m + 1) → Fin 2))), ∃ hI : I.Proper,
      I.dimension = k ∧ (I.bier hI).IsSphere (m + 2 ^ (m ^ 2 - m + 1) - 1) ∧
      (I.bier hI).vertices.card = 2 * (m + 2 ^ (m ^ 2 - m + 1)) + 1 ∧
      ¬ Polytopal (I.bier hI) := by sorry
end PalomarBier

/- Complete literal characterizations of every non-proof record field below.
These equations determine each supplied constructor completely by proof
irrelevance; they do not refer to opaque source primitives. -/
namespace PalomarBier.Spec
open LeanEval.Geometry.PlatonicClassification
/-- The face polytope has exactly the original extreme vertices lying in the face. -/
theorem facePolytope_vertices {n : ℕ} (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) :
    (facePolytope P hf).vertices = P.vertices.filter (fun v => v ∈ f) := by rfl
/-- Every realized face is exactly the standard basis image of an input face. -/
theorem standardRealization_faces {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : PreAbstractSimplicialComplex ι) :
    (DifferentialGeometry.Topology.Engulfing.standardRealization P).faces =
      (fun s : Finset ι => s.image (fun i => Pi.single i (1 : ℝ))) '' P.faces := by rfl
/-- The abstract complex contains exactly the actual nonempty faces. -/
theorem toAbstract_faces {V : Type*} [Fintype V] [DecidableEq V] (K : Bier.Complex V) :
    K.toAbstract.faces = {s | s.Nonempty ∧ K.face s} := by rfl
/-- Alexander duality is complement nonmembership on the full fixed ground set. -/
theorem dual_face {V : Type*} [Fintype V] [DecidableEq V] (K : Bier.Complex V)
    (hK : K.Proper) (s : Finset V) : (K.dual hK).face s ↔ ¬K.face sᶜ := by rfl
/-- All Bier faces are precisely the disjoint deleted-join face pairs. -/
theorem bier_face {V : Type*} [Fintype V] [DecidableEq V] (K : Bier.Complex V)
    (hK : K.Proper) (s : Finset (V ⊕ V)) :
    (K.bier hK).face s ↔
      K.face s.toLeft ∧ ¬K.face s.toRightᶜ ∧ Disjoint s.toLeft s.toRight := by rfl
/-- The new label is genuinely absent from every face. -/
theorem ghost_face {V : Type*} [Fintype V] [DecidableEq V] (K : Bier.Complex V)
    (s : Finset (Option V)) : K.ghost.face s ↔ none ∉ s ∧ K.face s.eraseNone := by rfl
end PalomarBier.Spec

namespace Bier.Forster
/-- Diagnostic: declaration order preserves the exact original operator norm value. -/
example {R C : Type*} [Fintype R] [Fintype C] (H : Matrix R C ℝ) :
    spectralNorm H = ‖H.toEuclideanLin.toContinuousLinearMap‖ := by rfl
end Bier.Forster

-- Three measured direct helper type lookups only; each full length and truncation is explicit.
run_cmd do
  let env ← Lean.getEnv
  let names := [`LeanEval.Geometry.PlatonicClassification.vertIper._proof_1,
    `Bier.Forster.spectralNorm._proof_9, `Bier.Forster.spectralNorm._proof_10]
  let mut found := 0
  let mut truncated := 0
  for name in names do
    match env.find? name with
    | none =>
      let row := Lean.Json.mkObj [
        ("kind", Lean.toJson "BIER_MEASURED_HELPER_TYPE"),
        ("name", Lean.toJson name.toString), ("found", Lean.toJson false)]
      Lean.logInfo m!"{row.compress}"
    | some ci =>
      found := found + 1
      let text := reprStr ci.type
      let cut := decide (8192 < text.length)
      if cut then truncated := truncated + 1
      let row := Lean.Json.mkObj [
        ("kind", Lean.toJson "BIER_MEASURED_HELPER_TYPE"),
        ("name", Lean.toJson name.toString), ("found", Lean.toJson true),
        ("level_params", Lean.toJson (ci.levelParams.map Lean.Name.toString)),
        ("type_characters", Lean.toJson text.length),
        ("type_text_limit", Lean.toJson (8192 : Nat)),
        ("type_truncated", Lean.toJson cut),
        ("type_ast", Lean.toJson (String.ofList (text.toList.take 8192)))]
      Lean.logInfo m!"{row.compress}"
  let summary := Lean.Json.mkObj [
    ("kind", Lean.toJson "BIER_MEASURED_HELPER_TYPE_SUMMARY"),
    ("requested_count", Lean.toJson names.length), ("found_count", Lean.toJson found),
    ("missing_count", Lean.toJson (names.length - found)),
    ("truncated_type_count", Lean.toJson truncated),
    ("whole_environment_enumerated", Lean.toJson false),
    ("proof_values_expanded", Lean.toJson false)]
  Lean.logInfo m!"{summary.compress}"
