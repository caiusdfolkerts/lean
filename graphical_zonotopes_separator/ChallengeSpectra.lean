module
public import Mathlib
/-! # Supplementary graphical-zonotope supports and dimension spectra
These endpoints retain actual convex bodies, Minkowski sums, the standard
integer lattice, full positive dimension spectra, prescribed coordinates,
sharp real dilation minima and both complementary Boolean summands.
Every definition is literal and every construction proof in the statement
semantics is genuine; only the selected theorem conclusions use placeholders.
This supplementary entry does not claim coverage of missing supporting
Proposition5.5 or PropositionA.1.
-/
@[expose] public section
noncomputable section
open Set Finset
open scoped BigOperators Pointwise Classical
namespace PalomarGraphicalSpectra
section Basic
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Real functions on the complete finite subset lattice. -/
abbrev SetFunction (V : Type*) := Finset V → ℝ

/-- The ordinary supermodular inequality for every two subsets. -/
def Supermodular (z : SetFunction V) : Prop :=
  ∀ A B, z A + z B ≤ z (A ∪ B) + z (A ∩ B)

/-- Value zero on the empty subset. -/
def Normalized (z : SetFunction V) : Prop := z ∅ = 0

/-- Both constant and singleton translation data vanish. -/
def TranslationNormalized (z : SetFunction V) : Prop :=
  Normalized z ∧ ∀ v, z {v} = 0

/-- The ordinary elemental supermodular difference. -/
def delta (z : SetFunction V) (u v : V) (S : Finset V) : ℝ :=
  z (insert u (insert v S)) - z (insert u S) - z (insert v S) + z S

/-- The sum over the specified actual coordinates. -/
def subsetSum (x : V → ℝ) (S : Finset V) : ℝ := ∑ v ∈ S, x v

/-- The actual lower base polytope cut out by every subset inequality. -/
def basePolytope (z : SetFunction V) : Set (V → ℝ) :=
  {x | subsetSum x univ = z univ ∧ ∀ S, z S ≤ subsetSum x S}

/-- Extremality by the decomposition property in the translation-normalized supermodular cone. -/
def ExtremeSupermodular (z : SetFunction V) : Prop :=
  TranslationNormalized z ∧ Supermodular z ∧ z ≠ 0 ∧
    ∀ f g : SetFunction V,
      TranslationNormalized f → TranslationNormalized g →
      Supermodular f → Supermodular g → f + g = z →
      ∃ a : ℝ, 0 ≤ a ∧ f = a • z

/-- Indecomposability against arbitrary actual compact convex Minkowski summands. -/
def MinkowskiIndecomposable (Q : Set (V → ℝ)) : Prop :=
  Q.Nonempty ∧ ∀ P R : Set (V → ℝ),
    IsCompact P → IsCompact R → Convex ℝ P → Convex ℝ R →
    P + R = Q → ∃ (a : ℝ) (t : V → ℝ), 0 ≤ a ∧ P = ({t} : Set (V → ℝ)) + a • Q

/-- The actual unordered two-element edge sets of the graph. -/
def edgeFamily (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact univ.filter (fun C => C.card = 2 ∧ ∀ u ∈ C, ∀ v ∈ C, u ≠ v → G.Adj u v)

/-- The standard coordinate basis vector. -/
def basisVector (v : V) : V → ℝ := Pi.single v 1

/-- The convex hull of the specified standard coordinate vectors. -/
def coordinateSimplex (C : Finset V) : Set (V → ℝ) :=
  convexHull ℝ (basisVector '' (C : Set V))

/-- The actual Minkowski sum of the graph edge segments. -/
def graphicalZonotope (G : SimpleGraph V) : Set (V → ℝ) :=
  ∑ C ∈ edgeFamily G, coordinateSimplex C

/-- Existence of an actual nonempty compact convex complementary summand. -/
def IsMinkowskiSummand (Q Z : Set (V → ℝ)) : Prop :=
  ∃ R : Set (V → ℝ), IsCompact R ∧ Convex ℝ R ∧ R.Nonempty ∧ Q+R=Z

/-- Actual summand status after some positive real dilation. -/
def IsWeakMinkowskiSummand (Q Z : Set (V → ℝ)) : Prop :=
  ∃ a : ℝ, 0< a ∧ IsMinkowskiSummand Q (a • Z)

/-- The complete nondegenerate exposed segment face of a linear functional. -/
def IsExposedSegment (Q : Set (V → ℝ)) (p q : V → ℝ) : Prop :=
  p ≠ q ∧ ∃ ℓ : (V → ℝ) →ₗ[ℝ] ℝ, ∃ a : ℝ,
    (∀ x ∈ Q, a ≤ ℓ x) ∧ {x ∈ Q | ℓ x = a} = segment ℝ p q

/-- An actual exposed segment parallel to the stated standard root. -/
def ActualRootEdge (Q : Set (V → ℝ)) (u v : V) : Prop :=
  u ≠ v ∧ ∃ p q, IsExposedSegment Q p q ∧
    ∃ a : ℝ, a ≠ 0 ∧ q-p = a • (basisVector u-basisVector v)

/-- An actual finite convex hull. -/
def IsFinitePolytope (Q : Set (V → ℝ)) : Prop :=
  ∃ s : Finset (V → ℝ), convexHull ℝ (s : Set (V → ℝ)) = Q

/-- Indecomposability against arbitrary actual finite polytopes. -/
def PolytopalMinkowskiIndecomposable (Q : Set (V → ℝ)) : Prop :=
  Q.Nonempty ∧ ∀ P R : Set (V → ℝ),IsFinitePolytope P → IsFinitePolytope R →
    P+R=Q → ∃ (a : ℝ) (t : V → ℝ),0≤ a ∧ P=({t} : Set (V → ℝ))+a • Q

/-- Full affine dimension in the coordinate-sum hyperplane. -/
def FullDimension (Q : Set (V → ℝ)) : Prop :=
  Module.finrank ℝ (vectorSpan ℝ Q) = Fintype.card V - 1

/-- Integer values on every subset. -/
def IntegerValued (z : SetFunction V) : Prop := ∀ S, ∃ a : ℤ, z S = (a : ℝ)

/-- The actual convex hull of finitely many standard integer vectors. -/
def LatticePolytope (Q : Set (V → ℝ)) : Prop :=
  ∃ P : Finset (V → ℤ), Q = convexHull ℝ ((fun x : V → ℤ => fun v => (x v : ℝ)) '' (P : Set (V → ℤ)))

/-- Every elemental difference on a nonedge is zero. -/
def Graphical (G : SimpleGraph V) (z : SetFunction V) : Prop :=
  ∀ u v, u ≠ v → ¬G.Adj u v → ∀ S, u ∉ S → v ∉ S → delta z u v S = 0

/-- The infimum of each actual coordinate sum over the set. -/
def lowerSupport (P : Set (V → ℝ)) (S : Finset V) : ℝ :=
  sInf ((fun x => subsetSum x S) '' P)

/-- Every actual lower-support elemental slack is zero or one. -/
def BooleanElemental (Q : Set (V → ℝ)) : Prop :=
  ∀ u v, u ≠ v → ∀ S : Finset V, u ∉ S → v ∉ S →
    delta (lowerSupport Q) u v S = 0 ∨ delta (lowerSupport Q) u v S = 1

/-- Full-dimensional lattice indecomposable actual summand at the specified real dilation. -/
def FullLatticeSummandAt (G : SimpleGraph V) (a : ℝ) : Prop :=
  ∃ Q : Set (V → ℝ), LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
    FullDimension Q ∧ IsMinkowskiSummand Q (a • graphicalZonotope G)

/-- The supremum of dimensions of actual indecomposable polytopal weak summands. -/
def maximumIndecomposableDimension (G : SimpleGraph V) : ℕ :=
  sSup {d : ℕ | ∃ Q : Set (V → ℝ), IsFinitePolytope Q ∧
    MinkowskiIndecomposable Q ∧ IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
    Module.finrank ℝ (vectorSpan ℝ Q) = d}

theorem actualRootEdge_symm {Q : Set (V → ℝ)} {u v : V}
    (h : ActualRootEdge Q u v) : ActualRootEdge Q v u := by
  obtain ⟨huv,p,q,hface,a,ha,he⟩ := h
  refine ⟨Ne.symm huv,p,q,hface,-a,neg_ne_zero.mpr ha,?_⟩
  rw [he,neg_smul,smul_sub,smul_sub]
  abel
/-- The graph of actual standard-root exposed edge directions. -/
def actualDirectionGraph (Q : Set (V → ℝ)) : SimpleGraph V where
  Adj := ActualRootEdge Q
  symm := ⟨fun _ _ => actualRootEdge_symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Join of the complete s-clique and k isolated outer vertices. -/
def cliqueBook (s k : ℕ) : SimpleGraph (Fin s ⊕ Fin k) where
  Adj u v := u ≠ v ∧ (u.isLeft ∨ v.isLeft)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
/-- The exact clique separator capacity from Theorem7.1. -/
def cliqueCapacity (s : ℕ) : ℕ :=
  s.choose 2 * 2^(s-2) - (2^s-s-1) + 1
/-- The lower endpoint in the high-count construction of Theorem7.10. -/
def bookUpperIntervalStart (s : ℕ) : ℕ :=
  (s-2)*2^(s-1)+2*s-2-s.choose 2
/-- The actual complete four-partite graph on the literal disjoint coordinate sets. -/
def fourPartite (a : Fin 4 → ℕ) : SimpleGraph (Σ i : Fin 4, Fin (a i)) :=
  SimpleGraph.completeMultipartiteGraph (fun i => Fin (a i))
/-- The complete four-partite graph with two singleton parts. -/
def twoSingletonGraph (p b : ℕ) := fourPartite ![1,1,p,b]

/-- Every coordinate outside U is constant on the actual body. -/
def FixesOutside (Q : Set (V → ℝ)) (U : Finset V) : Prop :=
  ∀ u, u ∉ U → ∃ c : ℝ, ∀ x ∈ Q, x u = c
/-- Exact dimension |U|-1 and fixed outside coordinates in the original ambient space. -/
def HasFullSupportedSummand (G : SimpleGraph V) (U : Finset V) : Prop :=
  ∃ Q : Set (V → ℝ), IsFinitePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧
    IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
    Module.finrank ℝ (vectorSpan ℝ Q) = U.card - 1 ∧ FixesOutside Q U
/-- Hubs in the prescribed original coordinate set. -/
def hubs {s k : ℕ} (U : Finset (Fin s ⊕ Fin k)) : Finset (Fin s) :=
  univ.filter (fun i => Sum.inl i ∈ U)
/-- Outer vertices in the prescribed original coordinate set. -/
def outers {s k : ℕ} (U : Finset (Fin s ⊕ Fin k)) : Finset (Fin k) :=
  univ.filter (fun j => Sum.inr j ∈ U)
/-- The smallest positive real dilation with a full-dimensional lattice indecomposable summand. -/
def LeastFullLatticeDilation (G : SimpleGraph V) (a : ℝ) : Prop :=
  0 < a ∧ FullLatticeSummandAt G a ∧
    ∀ b : ℝ, 0 < b → FullLatticeSummandAt G b → a ≤ b
namespace Path
def graph (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ u.val ≤ v.val + 3 ∧ v.val ≤ u.val + 3
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
end Path
namespace PathJoin
/-- Two hubs and a path with n+2 vertices, in literal integer coordinates. -/
abbrev Vertex (n : ℕ) := Fin (n+4)
/-- Symmetry of the explicit join adjacency formula. -/
theorem adjacency_symm {n : ℕ} (u v : Vertex n)
    (h : u ≠ v ∧ (u.val < 2 ∨ v.val < 2 ∨ u.val+1 = v.val ∨ v.val+1 = u.val)) :
    v ≠ u ∧ (v.val < 2 ∨ u.val < 2 ∨ v.val+1 = u.val ∨ u.val+1 = v.val) := by
  tauto
/-- The actual graph K2 joined to the path on n+2 vertices. -/
def graph (n : ℕ) : SimpleGraph (Vertex n) where
  Adj u v := u ≠ v ∧ (u.val < 2 ∨ v.val < 2 ∨ u.val+1 = v.val ∨ v.val+1 = u.val)
  symm := ⟨fun u v => adjacency_symm u v⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
end PathJoin
namespace DoubledParts
/-- Coordinates of the doubled-part graph after deleting the second vertex of the marked part. -/
abbrev SingletonVertices {I : Type*} (a : I) := {v : I × Fin 2 // v ≠ (a,1)}
/-- The literal complete multipartite graph with one singleton and all other parts doubled. -/
def singletonGraph {I : Type*} (a : I) : SimpleGraph (SingletonVertices a) where
  Adj u v := u.val.1 ≠ v.val.1
  symm := ⟨fun _ _ => Ne.symm⟩
  loopless := ⟨fun _ h => h rfl⟩
end DoubledParts


/-- Complete graph on the given active coordinates, with all others isolated. -/
def cliqueGraph (C : Finset V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ u ∈ C ∧ v ∈ C
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
/-- Exactly the star attaching a fresh vertex to the three displayed vertices. -/
def attachmentStar (u : V) (T : Finset V) : SimpleGraph V where
  Adj v w := v ≠ w ∧ ((v = u ∧ w ∈ T) ∨ (w = u ∧ v ∈ T))
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
/-- A tetrahedron followed by fresh-vertex attachments along existing triangles. -/
inductive ThreeTreeOn : Finset V → SimpleGraph V → Prop
  | tetrahedron (C : Finset V) (hC : C.card = 4) : ThreeTreeOn C (cliqueGraph C)
  | attach {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
      (u : V) (hu : u ∉ S) (T : Finset V) (hT : T.card = 3)
      (hTS : T ⊆ S) (hcl : G.IsClique T) :
      ThreeTreeOn (insert u S) (G ⊔ attachmentStar u T)
/-- A three-tree on the complete ambient coordinate set. -/
def IsThreeTree (G : SimpleGraph V) : Prop := ThreeTreeOn univ G
/-- The complete actual collection of four-cliques. -/
def tetrahedra (G : SimpleGraph V) : Finset (Finset V) :=
  univ.filter (fun C => C.card = 4 ∧ G.IsClique C)
/-- The number of four-cliques containing the displayed triangle. -/
def triangleMultiplicity (G : SimpleGraph V) (T : Finset V) : ℕ :=
  ((tetrahedra G).filter (fun C => T ⊆ C)).card
/-- Every triangle lies in at most three four-cliques. -/
def Admissible (G : SimpleGraph V) : Prop :=
  ∀ T : Finset V, T.card = 3 → G.IsClique T → triangleMultiplicity G T ≤ 3
/-- A same-ground-set subgraph of a three-tree; all graphs on ≤3 vertices are included. -/
def IsPartialThreeTree (G : SimpleGraph V) : Prop :=
  Fintype.card V ≤ 3 ∨ ∃ H : SimpleGraph V, IsThreeTree H ∧ G ≤ H
/-- A spanning admissible three-tree, with no vertices omitted. -/
def HasAdmissibleSpanningThreeTree (G : SimpleGraph V) : Prop :=
  ∃ H : SimpleGraph V, H ≤ G ∧ IsThreeTree H ∧ Admissible H
/-- Ambient induced graph, retaining the original coordinate set. -/
def inducedOn (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ S ∧ v ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩
/-- Named symmetry proof fixes the literal tetrahedron-graph constructor. -/
theorem tetrahedronIntersection_symm (C D : Finset V) (h : 3 ≤ (C ∩ D).card) :
    3 ≤ (D ∩ C).card := by
  rw [Finset.inter_comm] at h
  exact h
/-- Tetrahedra are adjacent exactly when distinct and sharing at least a triangle. -/
def tetrahedronGraph (F : Finset (Finset V)) : SimpleGraph {C : Finset V // C ∈ F} where
  Adj C D := C ≠ D ∧ 3 ≤ (C.1 ∩ D.1).card
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1,tetrahedronIntersection_symm _ _ h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
/-- Nonempty triangle-connected four-clique families, with each triangle in ≤3 members. -/
def IsAdmissibleCliqueCollection (G : SimpleGraph V) (F : Finset (Finset V)) : Prop :=
  F.Nonempty ∧ F ⊆ tetrahedra G ∧ (tetrahedronGraph F).Preconnected ∧
    ∀ T : Finset V,T.card = 3 → (F.filter (fun C => T ⊆ C)).card ≤ 3
/-- All admissible clique collections, with no optimizer selected abstractly. -/
def admissibleCliqueCollections (G : SimpleGraph V) : Finset (Finset (Finset V)) :=
  univ.filter (IsAdmissibleCliqueCollection G)
/-- The literal finite maximum M(G), with the empty maximum equal to zero. -/
def maximumAdmissibleCliqueCount (G : SimpleGraph V) : ℕ :=
  (admissibleCliqueCollections G).sup Finset.card
/-- All four exact cases, including triangles without tetrahedra and edgeless graphs. -/
def partialThreeTreeDimension (G : SimpleGraph V) : ℕ :=
  if (tetrahedra G).Nonempty then maximumAdmissibleCliqueCount G+2
  else if ∃ T : Finset V,T.card = 3 ∧ G.IsClique T then 2
  else if ∃ u v : V,G.Adj u v then 1 else 0
/-- Exact dependence of the original set function on displayed coordinates. -/
def DependsOn (z : SetFunction V) (S : Finset V) : Prop := ∀ T,z T = z (T ∩ S)
/-- Precisely the nonzero four-subset coefficients of the displayed function. -/
def fourFamily (y : SetFunction V) : Finset (Finset V) :=
  univ.filter (fun C => C.card = 4 ∧ y C ≠ 0)
/-- Named symmetry proof fixes the complete actual four-coefficient support graph. -/
theorem fourFamilyEdges_symm (y : SetFunction V) (u v : V)
    (h : u ≠ v ∧ ∃ C ∈ fourFamily y, u ∈ C ∧ v ∈ C) :
    v ≠ u ∧ ∃ C ∈ fourFamily y, v ∈ C ∧ u ∈ C := by
  obtain ⟨huv,C,hC,hu,hv⟩ := h
  exact ⟨Ne.symm huv,C,hC,hv,hu⟩
/-- All and only the edges in a nonzero four-coefficient support. -/
def edgeGraph (y : SetFunction V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ C ∈ fourFamily y,u ∈ C ∧ v ∈ C
  symm := ⟨fourFamilyEdges_symm y⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
namespace TreeJoin
/-- The literal adjacency relation for a new universal vertex. -/
def hubAdjacency (T : SimpleGraph V) (x y : V ⊕ Fin 1) : Prop :=
  match x,y with
  | .inl u,.inl v => T.Adj u v
  | .inl _,.inr _ => True
  | .inr _,.inl _ => True
  | .inr _,.inr _ => False
theorem hubAdjacency_symm (T : SimpleGraph V) (x y : V ⊕ Fin 1)
    (h : hubAdjacency T x y) : hubAdjacency T y x := by
  cases x <;> cases y
  · exact h.symm
  · exact h
  · exact h
  · exact h
theorem hubAdjacency_irrefl (T : SimpleGraph V) (x : V ⊕ Fin 1) : ¬hubAdjacency T x x := by
  cases x
  · exact T.irrefl
  · exact id
/-- Add one universal vertex, preserving every original vertex. -/
def addHub (T : SimpleGraph V) : SimpleGraph (V ⊕ Fin 1) where
  Adj := hubAdjacency T
  symm := ⟨hubAdjacency_symm T⟩
  loopless := ⟨hubAdjacency_irrefl T⟩
/-- The literal join of the original graph with a two-clique. -/
def graph (T : SimpleGraph V) : SimpleGraph ((V ⊕ Fin 1) ⊕ Fin 1) := addHub (addHub T)
/-- The maximum number of vertices in a nonempty induced subcubic subtree. -/
def s3 (T : SimpleGraph V) : ℕ :=
  (univ.filter (fun U : Finset V => (T.comap (Subtype.val : U → V)).IsTree ∧
    (T.comap (Subtype.val : U → V)).maxDegree ≤ 3)).sup Finset.card
end TreeJoin
open scoped Graph
/-
Drawing predicate adapted from Álvaro Begué's Jordan–Schönflies plane-graph
formalization, preserved at source/verified/parts/part025.lean.
Copyright (c)2026 Álvaro Begué. Released under the Apache2.0 license.
-/
namespace PlaneDrawing
/-- The actual Euclidean plane with its standard inner product topology. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)
/-- The full edge arc, parametrized on the closed unit interval. -/
def edgeArc {β : Type*} (drawing : β → ℝ → Plane) (e : β) : Set Plane :=
  drawing e '' (Set.Icc (0 : ℝ) (1 : ℝ))
/-- Continuous simple arcs with correct endpoints, no extra vertices, and only common-vertex intersections. -/
structure IsDrawing {β : Type*} (G : Graph Plane β) (drawing : β → ℝ → Plane) : Prop where
  edge_param : ∀ ⦃e⦄, e ∈ E(G) →
    ContinuousOn (drawing e) (Set.Icc (0 : ℝ) (1 : ℝ)) ∧ Set.InjOn (drawing e) (Set.Icc (0 : ℝ) (1 : ℝ)) ∧
      G.IsLink e (drawing e 0) (drawing e 1)
  vertex_mem_edgeArc : ∀ ⦃e x y v⦄, G.IsLink e x y → v ∈ V(G) → v ∈ edgeArc drawing e →
    v = x ∨ v = y
  edge_inter : ∀ ⦃e f : β⦄, e ∈ E(G) → f ∈ E(G) → e ≠ f →
    ∀ ⦃p⦄, p ∈ edgeArc drawing e → p ∈ edgeArc drawing f →
      p ∈ V(G) ∧ G.Inc e p ∧ G.Inc f p
/-- Place the original vertices in the plane, preserving every unordered edge label. -/
def planeGraph (G : SimpleGraph V) (p : V → Plane) : Graph Plane (Sym2 V) :=
  (Graph.ofSimpleGraph G).map p
end PlaneDrawing
/-- Genuine topological planarity: injective points and arbitrary simple continuous edge arcs. -/
def HasPlaneDrawing (G : SimpleGraph V) : Prop :=
  ∃ p : V → PlaneDrawing.Plane, Function.Injective p ∧
    ∃ drawing : Sym2 V → ℝ → PlaneDrawing.Plane,
      PlaneDrawing.IsDrawing (PlaneDrawing.planeGraph G p) drawing
namespace TetrahedronComponents
/-- Actual connected components of the triangle-adjacency graph of all tetrahedra. -/
abbrev Component (G : SimpleGraph V) := (tetrahedronGraph (tetrahedra G)).ConnectedComponent
noncomputable instance componentFintype (G : SimpleGraph V) : Fintype (Component G) :=
  @Fintype.ofFinite _ (Quot.finite _)
/-- Every tetrahedron lying in the specified component, with no representatives chosen. -/
def family (G : SimpleGraph V) (c : Component G) : Finset (Finset V) :=
  (tetrahedra G).filter (fun C => ∃ hC : C ∈ tetrahedra G,
    (tetrahedronGraph (tetrahedra G)).connectedComponentMk ⟨C,hC⟩ = c)
/-- The complete vertex union of the component. -/
def vertices (G : SimpleGraph V) (c : Component G) : Finset V := (family G c).biUnion id
/-- Exact finite maximum of |V(C)|−1, including zero for an empty component collection. -/
def maximumDimension (G : SimpleGraph V) : ℕ :=
  (univ : Finset (Component G)).sup (fun c => (vertices G c).card - 1)
end TetrahedronComponents
/-- The exact tetrahedron-component maximum, then triangle, edge and empty fallback cases. -/
def planarComponentDimension (G : SimpleGraph V) : ℕ :=
  if (tetrahedra G).Nonempty then TetrahedronComponents.maximumDimension G
  else if ∃ T : Finset V,T.card = 3 ∧ G.IsClique T then 2
  else if ∃ u v : V,G.Adj u v then 1 else 0
/-- Every actual graph triangle, including boundary triangles in no tetrahedron. -/
def triangles (G : SimpleGraph V) : Finset (Finset V) :=
  univ.filter (fun T => T.card = 3 ∧ G.IsClique T)
abbrev CliqueTriangleNode (G : SimpleGraph V) := ↥(tetrahedra G) ⊕ ↥(triangles G)
def incidenceAdjacency (G : SimpleGraph V) (x y : CliqueTriangleNode G) : Prop :=
  match x,y with
  | Sum.inl C,Sum.inr T => T.1 ⊆ C.1
  | Sum.inr T,Sum.inl C => T.1 ⊆ C.1
  | _,_ => False
theorem incidenceAdjacency_symm (G : SimpleGraph V) (x y : CliqueTriangleNode G)
    (h : incidenceAdjacency G x y) : incidenceAdjacency G y x := by
  cases x <;> cases y <;> exact h
theorem incidenceAdjacency_irrefl (G : SimpleGraph V) (x : CliqueTriangleNode G) :
    ¬incidenceAdjacency G x x := by
  cases x <;> exact id
/-- The complete literal bipartite incidence graph of tetrahedra and triangles. -/
def cliqueTriangleIncidence (G : SimpleGraph V) : SimpleGraph (CliqueTriangleNode G) where
  Adj := incidenceAdjacency G
  symm := ⟨incidenceAdjacency_symm G⟩
  loopless := ⟨incidenceAdjacency_irrefl G⟩


end Basic
variable {V : Type*} [Fintype V] [LinearOrder V]


/-- Corollary5.2 of paper.pdf, with literal actual-body and graph semantics. -/
theorem paper_corollary_5_2 {n : ℕ} (hn : 4 ≤ n) (G : SimpleGraph (Fin n))
    (hG : ∃ Q : Set (Fin n → ℝ),IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G)) :
    (∀ B : Finset (Fin n),
      2 ≤ Nat.card ((G.induce ((B : Set (Fin n))ᶜ)).ConnectedComponent) →
      ∃ T : Finset (Fin n),T ⊆ B ∧ T.card = 3 ∧ G.IsClique T) ∧
    (∀ B : Finset (Fin n),B.card < 3 →
      (G.induce ((B : Set (Fin n))ᶜ)).Connected) := by sorry

/-- Corollary5.3 of paper.pdf, with literal actual-body and graph semantics. -/
theorem triangle_components_le_three {n : ℕ} (hn : 2 ≤ n) {G : SimpleGraph (Fin n)}
    (h : ∃ Q : Set (Fin n → ℝ),IsFinitePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧
      FullDimension Q ∧ IsWeakMinkowskiSummand Q (graphicalZonotope G))
    (T : Finset (Fin n)) (hT : T.card = 3) (hc : G.IsClique T) :
    Nat.card ((G.induce ((T : Set (Fin n))ᶜ)).ConnectedComponent) ≤ 3 := by sorry

/-- Corollary6.7 of paper.pdf, with literal actual-body and graph semantics. -/
theorem threeTree_dimension_and_spectrum {G : SimpleGraph V} (hG : IsThreeTree G) :
    maximumIndecomposableDimension G = maximumAdmissibleCliqueCount G+2 ∧
      ∀ d : ℕ,1 ≤ d → d ≤ maximumAdmissibleCliqueCount G+2 →
        ∃ Q : Set (V → ℝ), LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
          IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
          Module.finrank ℝ (vectorSpan ℝ Q) = d := by sorry

/-- Corollary6.8 of paper.pdf, with literal actual-body and graph semantics. -/
theorem partial_threeTree_piecewise_maximum {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) :
    maximumIndecomposableDimension G = partialThreeTreeDimension G := by sorry

/-- Corollaries6.7–6.8, full positive spectrum of paper.pdf, with literal actual-body and graph semantics. -/
theorem partial_threeTree_full_dimension_spectrum {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (d : ℕ) (hd : 1 ≤ d)
    (hmax : d ≤ maximumIndecomposableDimension G) :
    ∃ Q : Set (V → ℝ),LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = d := by sorry

/-- Corollary6.9, tree join of paper.pdf, with literal actual-body and graph semantics. -/
theorem paper_corollary_6_9_tree_join (T : SimpleGraph V) (hT : T.IsTree) :
    (sSup {d : ℕ | ∃ Q : Set (((V ⊕ Fin 1) ⊕ Fin 1) → ℝ),IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (TreeJoin.graph T)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=d})=TreeJoin.s3 T+1 ∧
    ((∃ Q : Set (((V ⊕ Fin 1) ⊕ Fin 1) → ℝ),IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (TreeJoin.graph T))) ↔ T.maxDegree≤3) ∧
    ∃ Q : Set (((V ⊕ Fin 1) ⊕ Fin 1) → ℝ),LatticePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (TreeJoin.graph T)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=TreeJoin.s3 T+1 := by sorry

/-- Corollary6.6 of paper.pdf, with literal actual-body and graph semantics. -/
theorem partial_threeTree_support_classification {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) (H : SimpleGraph V) :
    (∃ Q : Set (V → ℝ),IsFinitePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      3 ≤ Module.finrank ℝ (vectorSpan ℝ Q) ∧ actualDirectionGraph Q = H) ↔
    ∃ U : Finset V,H = inducedOn G U ∧ ThreeTreeOn U H ∧ Admissible H := by sorry

/-- Corollary6.9, three-hub book of paper.pdf, with literal actual-body and graph semantics. -/
theorem three_hub_book_maximum (k : ℕ) (hk : 1≤ k) :
    maximumIndecomposableDimension (cliqueBook 3 k)=min (k+2) 5 := by sorry

/-- Corollary8.5 of paper.pdf, with literal actual-body and graph semantics. -/
theorem paper_corollary_8_5 (p : ℕ) (hp : 2 ≤ p) :
    (∃ Q : Set ((Σ i : Fin 4,Fin (![1,1,p,2^p+p] i)) → ℝ),
      LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (twoSingletonGraph p (2^p+p)))) ∧
    ¬HasAdmissibleSpanningThreeTree (twoSingletonGraph p (2^p+p)) := by sorry

/-- Corollary4.4 of paper.pdf, with literal actual-body and graph semantics. -/
theorem refined_support_of_dimension_ge_three {G : SimpleGraph V}
    (hG : G.CliqueFree 5) {z : SetFunction V} (hz : ExtremeSupermodular z)
    (hgraph : Graphical G z)
    (hdim : 3 ≤ Module.finrank ℝ (vectorSpan ℝ (basePolytope z))) :
    ∃ y : SetFunction V,(∀ S,z S = ∑ C ∈ S.powerset,y C) ∧
      (fourFamily y).Nonempty ∧ (tetrahedronGraph (fourFamily y)).Preconnected ∧
      actualDirectionGraph (basePolytope z) = edgeGraph y ∧
      DependsOn z ((fourFamily y).biUnion id) := by sorry

/-- Corollary6.4 of paper.pdf, with literal actual-body and graph semantics. -/
theorem planar_full_iff_threeTree (G : SimpleGraph V) (hG : HasPlaneDrawing G)
    (hn : 4 ≤ Fintype.card V) :
    (∃ Q : Set (V → ℝ),IsFinitePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧
      FullDimension Q ∧ IsWeakMinkowskiSummand Q (graphicalZonotope G)) ↔ IsThreeTree G := by sorry

/-- Corollary6.5 of paper.pdf, with literal actual-body and graph semantics. -/
theorem planar_component_dimension_spectrum (G : SimpleGraph V) (hG : HasPlaneDrawing G) :
    (sSup {d : ℕ | ∃ Q : Set (V → ℝ),IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = d}) = planarComponentDimension G ∧
    ∀ d : ℕ,1 ≤ d → d ≤ planarComponentDimension G →
      ∃ Q : Set (V → ℝ),LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
        Module.finrank ℝ (vectorSpan ℝ Q) = d := by sorry

/-- Corollary6.7's incidence tree is derived from the actual recursive3tree. -/
theorem threeTree_incidence_isTree {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) : (cliqueTriangleIncidence G).IsTree := by sorry
/-- Corollary6.8's intrinsic incidence forest, including all small/empty cases. -/
theorem partial_threeTree_incidence_isAcyclic {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) : (cliqueTriangleIncidence G).IsAcyclic := by sorry
/-- Corollary6.9's Hamiltonian conclusion with an actual full lattice witness. -/
theorem hamiltonian_threeTree_lattice_witness (G : SimpleGraph V)
    (hG : IsThreeTree G) (hH : G.IsHamiltonian) :
    ∃ Q : Set (V → ℝ), LatticePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧ actualDirectionGraph Q = G := by sorry
/-- An internal coordinate order on every finite ground set. -/
def finiteVertexOrder (W : Type*) [Fintype W] : LinearOrder W :=
  LinearOrder.lift' (Fintype.equivFin W) (Fintype.equivFin W).injective
/-- Corollary6.4 on an arbitrary finite type; no drawing order is an assumption. -/
theorem planar_full_iff_threeTree_finite {W : Type*} [Fintype W] :
    letI : LinearOrder W := finiteVertexOrder W;
    ∀ G : SimpleGraph W, HasPlaneDrawing G → 4 ≤ Fintype.card W →
      ((∃ Q : Set (W → ℝ), IsFinitePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧
        FullDimension Q ∧ IsWeakMinkowskiSummand Q (graphicalZonotope G)) ↔ IsThreeTree G) := by sorry
/-- Corollary6.5 on every finite type, with complete literal component values. -/
theorem planar_component_dimension_spectrum_finite {W : Type*} [Fintype W] :
    letI : LinearOrder W := finiteVertexOrder W;
    ∀ G : SimpleGraph W, HasPlaneDrawing G →
      (sSup {d : ℕ | ∃ Q : Set (W → ℝ), IsFinitePolytope Q ∧
        PolytopalMinkowskiIndecomposable Q ∧ IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
        Module.finrank ℝ (vectorSpan ℝ Q) = d}) = planarComponentDimension G ∧
      ∀ d : ℕ, 1 ≤ d → d ≤ planarComponentDimension G →
        ∃ Q : Set (W → ℝ), LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧
          IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
          Module.finrank ℝ (vectorSpan ℝ Q) = d := by sorry

/-- Corollary6.6 with the exact |U|−1 dimension on the same actual support. -/
theorem partial_threeTree_polytope_support {G : SimpleGraph V}
    (hG : IsPartialThreeTree G) {Q : Set (V → ℝ)} (hQ : IsFinitePolytope Q)
    (hi : MinkowskiIndecomposable Q)
    (hw : IsWeakMinkowskiSummand Q (graphicalZonotope G))
    (hd : 3 ≤ Module.finrank ℝ (vectorSpan ℝ Q)) :
    ∃ U : Finset V,4 ≤ U.card ∧ actualDirectionGraph Q = inducedOn G U ∧
      ThreeTreeOn U (inducedOn G U) ∧ Admissible (inducedOn G U) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = U.card-1 := by sorry

/-- Corollary6.6 with the exact |U|−1 dimension on the same actual support. -/
theorem induced_admissible_threeTree_witness {G : SimpleGraph V} {U : Finset V}
    (hU : ThreeTreeOn U (inducedOn G U)) (hA : Admissible (inducedOn G U)) :
    ∃ Q : Set (V → ℝ),LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
      actualDirectionGraph Q = inducedOn G U ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = U.card-1 := by sorry

end PalomarGraphicalSpectra
