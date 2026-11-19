module
public import Mathlib
public import verified.extensions
/-! # Supplementary graphical-zonotope consequences and constructions
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
namespace PalomarGraphicalConsequences
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

theorem small_count_lattice_books (s k : ℕ) (hs : 2≤ s) (hk : 1≤ k)
    (hmax : k≤ s.choose 2) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(k : ℝ) • graphicalZonotope (cliqueBook s k) := by
  simpa only [SetFunction, Supermodular, Normalized, TranslationNormalized, delta, subsetSum, basePolytope, ExtremeSupermodular, MinkowskiIndecomposable, edgeFamily, basisVector, coordinateSimplex, graphicalZonotope, IsMinkowskiSummand, IsWeakMinkowskiSummand, IsExposedSegment, ActualRootEdge, IsFinitePolytope, PolytopalMinkowskiIndecomposable, FullDimension, maximumIndecomposableDimension, IntegerValued, LatticePolytope, Graphical, lowerSupport, BooleanElemental, FullLatticeSummandAt, actualDirectionGraph, cliqueBook, cliqueCapacity, fourPartite, twoSingletonGraph, LeastFullLatticeDilation, GraphicalZonotopes.SetFunction, GraphicalZonotopes.Supermodular, GraphicalZonotopes.Normalized, GraphicalZonotopes.TranslationNormalized, GraphicalZonotopes.delta, GraphicalZonotopes.subsetSum, GraphicalZonotopes.basePolytope, GraphicalZonotopes.ExtremeSupermodular, GraphicalZonotopes.MinkowskiIndecomposable, GraphicalZonotopes.edgeFamily, GraphicalZonotopes.basisVector, GraphicalZonotopes.coordinateSimplex, GraphicalZonotopes.graphicalZonotope, GraphicalZonotopes.IsMinkowskiSummand, GraphicalZonotopes.IsWeakMinkowskiSummand, GraphicalZonotopes.IsExposedSegment, GraphicalZonotopes.ActualRootEdge, GraphicalZonotopes.IsFinitePolytope, GraphicalZonotopes.PolytopalMinkowskiIndecomposable, GraphicalZonotopes.FullDimension, GraphicalZonotopes.maximumIndecomposableDimension, GraphicalZonotopes.IntegerValued, GraphicalZonotopes.LatticePolytope, GraphicalZonotopes.Graphical, GraphicalZonotopes.lowerSupport, GraphicalZonotopes.BooleanElemental, GraphicalZonotopes.FullLatticeSummandAt, GraphicalZonotopes.actualDirectionGraph, GraphicalZonotopes.cliqueBook, GraphicalZonotopes.cliqueCapacity, GraphicalZonotopes.fourPartite, GraphicalZonotopes.twoSingletonGraph, GraphicalZonotopes.LeastFullLatticeDilation, FixesOutside, HasFullSupportedSummand, GraphicalZonotopes.BookSpectrum.FixesOutside, GraphicalZonotopes.BookSpectrum.HasFullSupportedSummand, hubs, outers, GraphicalZonotopes.BookSpectrum.hubs, GraphicalZonotopes.BookSpectrum.outers, bookUpperIntervalStart, GraphicalZonotopes.BooleanModule.bookUpperIntervalStart, Path.graph, PathJoin.graph, GraphicalZonotopes.Path.graph, GraphicalZonotopes.PathJoin.graph] using
    GraphicalZonotopes.BooleanModule.small_count_lattice_books s k hs hk hmax

theorem threshold_book_interval {s k : ℕ} (hs : 3≤ s)
    (hklo : 2^(s-1)-s+1≤ k)
    (hkhi : k≤ cliqueCapacity s-cliqueCapacity (s-1)+1) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(k : ℝ) • graphicalZonotope (cliqueBook s k) := by
  simpa only [SetFunction, Supermodular, Normalized, TranslationNormalized, delta, subsetSum, basePolytope, ExtremeSupermodular, MinkowskiIndecomposable, edgeFamily, basisVector, coordinateSimplex, graphicalZonotope, IsMinkowskiSummand, IsWeakMinkowskiSummand, IsExposedSegment, ActualRootEdge, IsFinitePolytope, PolytopalMinkowskiIndecomposable, FullDimension, maximumIndecomposableDimension, IntegerValued, LatticePolytope, Graphical, lowerSupport, BooleanElemental, FullLatticeSummandAt, actualDirectionGraph, cliqueBook, cliqueCapacity, fourPartite, twoSingletonGraph, LeastFullLatticeDilation, GraphicalZonotopes.SetFunction, GraphicalZonotopes.Supermodular, GraphicalZonotopes.Normalized, GraphicalZonotopes.TranslationNormalized, GraphicalZonotopes.delta, GraphicalZonotopes.subsetSum, GraphicalZonotopes.basePolytope, GraphicalZonotopes.ExtremeSupermodular, GraphicalZonotopes.MinkowskiIndecomposable, GraphicalZonotopes.edgeFamily, GraphicalZonotopes.basisVector, GraphicalZonotopes.coordinateSimplex, GraphicalZonotopes.graphicalZonotope, GraphicalZonotopes.IsMinkowskiSummand, GraphicalZonotopes.IsWeakMinkowskiSummand, GraphicalZonotopes.IsExposedSegment, GraphicalZonotopes.ActualRootEdge, GraphicalZonotopes.IsFinitePolytope, GraphicalZonotopes.PolytopalMinkowskiIndecomposable, GraphicalZonotopes.FullDimension, GraphicalZonotopes.maximumIndecomposableDimension, GraphicalZonotopes.IntegerValued, GraphicalZonotopes.LatticePolytope, GraphicalZonotopes.Graphical, GraphicalZonotopes.lowerSupport, GraphicalZonotopes.BooleanElemental, GraphicalZonotopes.FullLatticeSummandAt, GraphicalZonotopes.actualDirectionGraph, GraphicalZonotopes.cliqueBook, GraphicalZonotopes.cliqueCapacity, GraphicalZonotopes.fourPartite, GraphicalZonotopes.twoSingletonGraph, GraphicalZonotopes.LeastFullLatticeDilation, FixesOutside, HasFullSupportedSummand, GraphicalZonotopes.BookSpectrum.FixesOutside, GraphicalZonotopes.BookSpectrum.HasFullSupportedSummand, hubs, outers, GraphicalZonotopes.BookSpectrum.hubs, GraphicalZonotopes.BookSpectrum.outers, bookUpperIntervalStart, GraphicalZonotopes.BooleanModule.bookUpperIntervalStart, Path.graph, PathJoin.graph, GraphicalZonotopes.Path.graph, GraphicalZonotopes.PathJoin.graph] using
    GraphicalZonotopes.BooleanModule.threshold_book_interval hs hklo hkhi

theorem two_threshold_four_bridge {k : ℕ} (hklo : 12≤ k) (hkhi : k≤14) :
    ∃ f : SetFunction (Fin 4⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook 4 k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin 4⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(((2*k : ℕ) : ℝ)) • graphicalZonotope (cliqueBook 4 k) := by
  simpa only [SetFunction, Supermodular, Normalized, TranslationNormalized, delta, subsetSum, basePolytope, ExtremeSupermodular, MinkowskiIndecomposable, edgeFamily, basisVector, coordinateSimplex, graphicalZonotope, IsMinkowskiSummand, IsWeakMinkowskiSummand, IsExposedSegment, ActualRootEdge, IsFinitePolytope, PolytopalMinkowskiIndecomposable, FullDimension, maximumIndecomposableDimension, IntegerValued, LatticePolytope, Graphical, lowerSupport, BooleanElemental, FullLatticeSummandAt, actualDirectionGraph, cliqueBook, cliqueCapacity, fourPartite, twoSingletonGraph, LeastFullLatticeDilation, GraphicalZonotopes.SetFunction, GraphicalZonotopes.Supermodular, GraphicalZonotopes.Normalized, GraphicalZonotopes.TranslationNormalized, GraphicalZonotopes.delta, GraphicalZonotopes.subsetSum, GraphicalZonotopes.basePolytope, GraphicalZonotopes.ExtremeSupermodular, GraphicalZonotopes.MinkowskiIndecomposable, GraphicalZonotopes.edgeFamily, GraphicalZonotopes.basisVector, GraphicalZonotopes.coordinateSimplex, GraphicalZonotopes.graphicalZonotope, GraphicalZonotopes.IsMinkowskiSummand, GraphicalZonotopes.IsWeakMinkowskiSummand, GraphicalZonotopes.IsExposedSegment, GraphicalZonotopes.ActualRootEdge, GraphicalZonotopes.IsFinitePolytope, GraphicalZonotopes.PolytopalMinkowskiIndecomposable, GraphicalZonotopes.FullDimension, GraphicalZonotopes.maximumIndecomposableDimension, GraphicalZonotopes.IntegerValued, GraphicalZonotopes.LatticePolytope, GraphicalZonotopes.Graphical, GraphicalZonotopes.lowerSupport, GraphicalZonotopes.BooleanElemental, GraphicalZonotopes.FullLatticeSummandAt, GraphicalZonotopes.actualDirectionGraph, GraphicalZonotopes.cliqueBook, GraphicalZonotopes.cliqueCapacity, GraphicalZonotopes.fourPartite, GraphicalZonotopes.twoSingletonGraph, GraphicalZonotopes.LeastFullLatticeDilation, FixesOutside, HasFullSupportedSummand, GraphicalZonotopes.BookSpectrum.FixesOutside, GraphicalZonotopes.BookSpectrum.HasFullSupportedSummand, hubs, outers, GraphicalZonotopes.BookSpectrum.hubs, GraphicalZonotopes.BookSpectrum.outers, bookUpperIntervalStart, GraphicalZonotopes.BooleanModule.bookUpperIntervalStart, Path.graph, PathJoin.graph, GraphicalZonotopes.Path.graph, GraphicalZonotopes.PathJoin.graph] using
    GraphicalZonotopes.BooleanModule.two_threshold_four_bridge hklo hkhi

theorem two_threshold_five_bridge {k : ℕ} (hklo : 39≤ k) (hkhi : k≤53) :
    ∃ f : SetFunction (Fin 5⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook 5 k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin 5⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(((2*k : ℕ) : ℝ)) • graphicalZonotope (cliqueBook 5 k) := by
  simpa only [SetFunction, Supermodular, Normalized, TranslationNormalized, delta, subsetSum, basePolytope, ExtremeSupermodular, MinkowskiIndecomposable, edgeFamily, basisVector, coordinateSimplex, graphicalZonotope, IsMinkowskiSummand, IsWeakMinkowskiSummand, IsExposedSegment, ActualRootEdge, IsFinitePolytope, PolytopalMinkowskiIndecomposable, FullDimension, maximumIndecomposableDimension, IntegerValued, LatticePolytope, Graphical, lowerSupport, BooleanElemental, FullLatticeSummandAt, actualDirectionGraph, cliqueBook, cliqueCapacity, fourPartite, twoSingletonGraph, LeastFullLatticeDilation, GraphicalZonotopes.SetFunction, GraphicalZonotopes.Supermodular, GraphicalZonotopes.Normalized, GraphicalZonotopes.TranslationNormalized, GraphicalZonotopes.delta, GraphicalZonotopes.subsetSum, GraphicalZonotopes.basePolytope, GraphicalZonotopes.ExtremeSupermodular, GraphicalZonotopes.MinkowskiIndecomposable, GraphicalZonotopes.edgeFamily, GraphicalZonotopes.basisVector, GraphicalZonotopes.coordinateSimplex, GraphicalZonotopes.graphicalZonotope, GraphicalZonotopes.IsMinkowskiSummand, GraphicalZonotopes.IsWeakMinkowskiSummand, GraphicalZonotopes.IsExposedSegment, GraphicalZonotopes.ActualRootEdge, GraphicalZonotopes.IsFinitePolytope, GraphicalZonotopes.PolytopalMinkowskiIndecomposable, GraphicalZonotopes.FullDimension, GraphicalZonotopes.maximumIndecomposableDimension, GraphicalZonotopes.IntegerValued, GraphicalZonotopes.LatticePolytope, GraphicalZonotopes.Graphical, GraphicalZonotopes.lowerSupport, GraphicalZonotopes.BooleanElemental, GraphicalZonotopes.FullLatticeSummandAt, GraphicalZonotopes.actualDirectionGraph, GraphicalZonotopes.cliqueBook, GraphicalZonotopes.cliqueCapacity, GraphicalZonotopes.fourPartite, GraphicalZonotopes.twoSingletonGraph, GraphicalZonotopes.LeastFullLatticeDilation, FixesOutside, HasFullSupportedSummand, GraphicalZonotopes.BookSpectrum.FixesOutside, GraphicalZonotopes.BookSpectrum.HasFullSupportedSummand, hubs, outers, GraphicalZonotopes.BookSpectrum.hubs, GraphicalZonotopes.BookSpectrum.outers, bookUpperIntervalStart, GraphicalZonotopes.BooleanModule.bookUpperIntervalStart, Path.graph, PathJoin.graph, GraphicalZonotopes.Path.graph, GraphicalZonotopes.PathJoin.graph] using
    GraphicalZonotopes.BooleanModule.two_threshold_five_bridge hklo hkhi

theorem book_upper_interval {s : ℕ} (hs : 5≤ s) {k : ℕ} (hklo : bookUpperIntervalStart s≤ k)
    (hkhi : k≤ cliqueCapacity s) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(((s-1)*k : ℕ) : ℝ) • graphicalZonotope (cliqueBook s k) := by
  simpa only [SetFunction, Supermodular, Normalized, TranslationNormalized, delta, subsetSum, basePolytope, ExtremeSupermodular, MinkowskiIndecomposable, edgeFamily, basisVector, coordinateSimplex, graphicalZonotope, IsMinkowskiSummand, IsWeakMinkowskiSummand, IsExposedSegment, ActualRootEdge, IsFinitePolytope, PolytopalMinkowskiIndecomposable, FullDimension, maximumIndecomposableDimension, IntegerValued, LatticePolytope, Graphical, lowerSupport, BooleanElemental, FullLatticeSummandAt, actualDirectionGraph, cliqueBook, cliqueCapacity, fourPartite, twoSingletonGraph, LeastFullLatticeDilation, GraphicalZonotopes.SetFunction, GraphicalZonotopes.Supermodular, GraphicalZonotopes.Normalized, GraphicalZonotopes.TranslationNormalized, GraphicalZonotopes.delta, GraphicalZonotopes.subsetSum, GraphicalZonotopes.basePolytope, GraphicalZonotopes.ExtremeSupermodular, GraphicalZonotopes.MinkowskiIndecomposable, GraphicalZonotopes.edgeFamily, GraphicalZonotopes.basisVector, GraphicalZonotopes.coordinateSimplex, GraphicalZonotopes.graphicalZonotope, GraphicalZonotopes.IsMinkowskiSummand, GraphicalZonotopes.IsWeakMinkowskiSummand, GraphicalZonotopes.IsExposedSegment, GraphicalZonotopes.ActualRootEdge, GraphicalZonotopes.IsFinitePolytope, GraphicalZonotopes.PolytopalMinkowskiIndecomposable, GraphicalZonotopes.FullDimension, GraphicalZonotopes.maximumIndecomposableDimension, GraphicalZonotopes.IntegerValued, GraphicalZonotopes.LatticePolytope, GraphicalZonotopes.Graphical, GraphicalZonotopes.lowerSupport, GraphicalZonotopes.BooleanElemental, GraphicalZonotopes.FullLatticeSummandAt, GraphicalZonotopes.actualDirectionGraph, GraphicalZonotopes.cliqueBook, GraphicalZonotopes.cliqueCapacity, GraphicalZonotopes.fourPartite, GraphicalZonotopes.twoSingletonGraph, GraphicalZonotopes.LeastFullLatticeDilation, FixesOutside, HasFullSupportedSummand, GraphicalZonotopes.BookSpectrum.FixesOutside, GraphicalZonotopes.BookSpectrum.HasFullSupportedSummand, hubs, outers, GraphicalZonotopes.BookSpectrum.hubs, GraphicalZonotopes.BookSpectrum.outers, bookUpperIntervalStart, GraphicalZonotopes.BooleanModule.bookUpperIntervalStart, Path.graph, PathJoin.graph, GraphicalZonotopes.Path.graph, GraphicalZonotopes.PathJoin.graph] using
    GraphicalZonotopes.BooleanModule.book_upper_interval hs hklo hkhi

theorem lattice_dimension_spectrum (s k d : ℕ) (hs : 2 ≤ s) (hk : 1 ≤ k)
    (hd : 1 ≤ d) (hmax : d ≤ min (s + k - 1) (s + cliqueCapacity s - 1)) :
    ∃ Q : Set ((Fin s ⊕ Fin k) → ℝ), LatticePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s k)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  simpa only [SetFunction, Supermodular, Normalized, TranslationNormalized, delta, subsetSum, basePolytope, ExtremeSupermodular, MinkowskiIndecomposable, edgeFamily, basisVector, coordinateSimplex, graphicalZonotope, IsMinkowskiSummand, IsWeakMinkowskiSummand, IsExposedSegment, ActualRootEdge, IsFinitePolytope, PolytopalMinkowskiIndecomposable, FullDimension, maximumIndecomposableDimension, IntegerValued, LatticePolytope, Graphical, lowerSupport, BooleanElemental, FullLatticeSummandAt, actualDirectionGraph, cliqueBook, cliqueCapacity, fourPartite, twoSingletonGraph, LeastFullLatticeDilation, GraphicalZonotopes.SetFunction, GraphicalZonotopes.Supermodular, GraphicalZonotopes.Normalized, GraphicalZonotopes.TranslationNormalized, GraphicalZonotopes.delta, GraphicalZonotopes.subsetSum, GraphicalZonotopes.basePolytope, GraphicalZonotopes.ExtremeSupermodular, GraphicalZonotopes.MinkowskiIndecomposable, GraphicalZonotopes.edgeFamily, GraphicalZonotopes.basisVector, GraphicalZonotopes.coordinateSimplex, GraphicalZonotopes.graphicalZonotope, GraphicalZonotopes.IsMinkowskiSummand, GraphicalZonotopes.IsWeakMinkowskiSummand, GraphicalZonotopes.IsExposedSegment, GraphicalZonotopes.ActualRootEdge, GraphicalZonotopes.IsFinitePolytope, GraphicalZonotopes.PolytopalMinkowskiIndecomposable, GraphicalZonotopes.FullDimension, GraphicalZonotopes.maximumIndecomposableDimension, GraphicalZonotopes.IntegerValued, GraphicalZonotopes.LatticePolytope, GraphicalZonotopes.Graphical, GraphicalZonotopes.lowerSupport, GraphicalZonotopes.BooleanElemental, GraphicalZonotopes.FullLatticeSummandAt, GraphicalZonotopes.actualDirectionGraph, GraphicalZonotopes.cliqueBook, GraphicalZonotopes.cliqueCapacity, GraphicalZonotopes.fourPartite, GraphicalZonotopes.twoSingletonGraph, GraphicalZonotopes.LeastFullLatticeDilation, FixesOutside, HasFullSupportedSummand, GraphicalZonotopes.BookSpectrum.FixesOutside, GraphicalZonotopes.BookSpectrum.HasFullSupportedSummand, hubs, outers, GraphicalZonotopes.BookSpectrum.hubs, GraphicalZonotopes.BookSpectrum.outers, bookUpperIntervalStart, GraphicalZonotopes.BooleanModule.bookUpperIntervalStart, Path.graph, PathJoin.graph, GraphicalZonotopes.Path.graph, GraphicalZonotopes.PathJoin.graph] using
    GraphicalZonotopes.BookSpectrum.lattice_dimension_spectrum s k d hs hk hd hmax

theorem positive_dimension_spectrum (s k d : ℕ) (hs : 2 ≤ s) (hk : 1 ≤ k)
    (hd : 1 ≤ d) :
    (∃ Q : Set ((Fin s ⊕ Fin k) → ℝ), IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s k)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = d) ↔
      d ≤ min (s + k - 1) (s + cliqueCapacity s - 1) := by
  simpa only [SetFunction, Supermodular, Normalized, TranslationNormalized, delta, subsetSum, basePolytope, ExtremeSupermodular, MinkowskiIndecomposable, edgeFamily, basisVector, coordinateSimplex, graphicalZonotope, IsMinkowskiSummand, IsWeakMinkowskiSummand, IsExposedSegment, ActualRootEdge, IsFinitePolytope, PolytopalMinkowskiIndecomposable, FullDimension, maximumIndecomposableDimension, IntegerValued, LatticePolytope, Graphical, lowerSupport, BooleanElemental, FullLatticeSummandAt, actualDirectionGraph, cliqueBook, cliqueCapacity, fourPartite, twoSingletonGraph, LeastFullLatticeDilation, GraphicalZonotopes.SetFunction, GraphicalZonotopes.Supermodular, GraphicalZonotopes.Normalized, GraphicalZonotopes.TranslationNormalized, GraphicalZonotopes.delta, GraphicalZonotopes.subsetSum, GraphicalZonotopes.basePolytope, GraphicalZonotopes.ExtremeSupermodular, GraphicalZonotopes.MinkowskiIndecomposable, GraphicalZonotopes.edgeFamily, GraphicalZonotopes.basisVector, GraphicalZonotopes.coordinateSimplex, GraphicalZonotopes.graphicalZonotope, GraphicalZonotopes.IsMinkowskiSummand, GraphicalZonotopes.IsWeakMinkowskiSummand, GraphicalZonotopes.IsExposedSegment, GraphicalZonotopes.ActualRootEdge, GraphicalZonotopes.IsFinitePolytope, GraphicalZonotopes.PolytopalMinkowskiIndecomposable, GraphicalZonotopes.FullDimension, GraphicalZonotopes.maximumIndecomposableDimension, GraphicalZonotopes.IntegerValued, GraphicalZonotopes.LatticePolytope, GraphicalZonotopes.Graphical, GraphicalZonotopes.lowerSupport, GraphicalZonotopes.BooleanElemental, GraphicalZonotopes.FullLatticeSummandAt, GraphicalZonotopes.actualDirectionGraph, GraphicalZonotopes.cliqueBook, GraphicalZonotopes.cliqueCapacity, GraphicalZonotopes.fourPartite, GraphicalZonotopes.twoSingletonGraph, GraphicalZonotopes.LeastFullLatticeDilation, FixesOutside, HasFullSupportedSummand, GraphicalZonotopes.BookSpectrum.FixesOutside, GraphicalZonotopes.BookSpectrum.HasFullSupportedSummand, hubs, outers, GraphicalZonotopes.BookSpectrum.hubs, GraphicalZonotopes.BookSpectrum.outers, bookUpperIntervalStart, GraphicalZonotopes.BooleanModule.bookUpperIntervalStart, Path.graph, PathJoin.graph, GraphicalZonotopes.Path.graph, GraphicalZonotopes.PathJoin.graph] using
    GraphicalZonotopes.BookSpectrum.positive_dimension_spectrum s k d hs hk hd

theorem prescribed_coordinate_criterion {s k : ℕ} (U : Finset ((Fin s ⊕ Fin k)))
    (hU : 2 ≤ U.card) :
    HasFullSupportedSummand (cliqueBook s k) U ↔
      (outers U).card = 0 ∨
      ((hubs U).card = 1 ∧ (outers U).card = 1) ∨
      (2 ≤ (hubs U).card ∧ 1 ≤ (outers U).card ∧
        (outers U).card ≤ cliqueCapacity (hubs U).card) := by
  simpa only [SetFunction, Supermodular, Normalized, TranslationNormalized, delta, subsetSum, basePolytope, ExtremeSupermodular, MinkowskiIndecomposable, edgeFamily, basisVector, coordinateSimplex, graphicalZonotope, IsMinkowskiSummand, IsWeakMinkowskiSummand, IsExposedSegment, ActualRootEdge, IsFinitePolytope, PolytopalMinkowskiIndecomposable, FullDimension, maximumIndecomposableDimension, IntegerValued, LatticePolytope, Graphical, lowerSupport, BooleanElemental, FullLatticeSummandAt, actualDirectionGraph, cliqueBook, cliqueCapacity, fourPartite, twoSingletonGraph, LeastFullLatticeDilation, GraphicalZonotopes.SetFunction, GraphicalZonotopes.Supermodular, GraphicalZonotopes.Normalized, GraphicalZonotopes.TranslationNormalized, GraphicalZonotopes.delta, GraphicalZonotopes.subsetSum, GraphicalZonotopes.basePolytope, GraphicalZonotopes.ExtremeSupermodular, GraphicalZonotopes.MinkowskiIndecomposable, GraphicalZonotopes.edgeFamily, GraphicalZonotopes.basisVector, GraphicalZonotopes.coordinateSimplex, GraphicalZonotopes.graphicalZonotope, GraphicalZonotopes.IsMinkowskiSummand, GraphicalZonotopes.IsWeakMinkowskiSummand, GraphicalZonotopes.IsExposedSegment, GraphicalZonotopes.ActualRootEdge, GraphicalZonotopes.IsFinitePolytope, GraphicalZonotopes.PolytopalMinkowskiIndecomposable, GraphicalZonotopes.FullDimension, GraphicalZonotopes.maximumIndecomposableDimension, GraphicalZonotopes.IntegerValued, GraphicalZonotopes.LatticePolytope, GraphicalZonotopes.Graphical, GraphicalZonotopes.lowerSupport, GraphicalZonotopes.BooleanElemental, GraphicalZonotopes.FullLatticeSummandAt, GraphicalZonotopes.actualDirectionGraph, GraphicalZonotopes.cliqueBook, GraphicalZonotopes.cliqueCapacity, GraphicalZonotopes.fourPartite, GraphicalZonotopes.twoSingletonGraph, GraphicalZonotopes.LeastFullLatticeDilation, FixesOutside, HasFullSupportedSummand, GraphicalZonotopes.BookSpectrum.FixesOutside, GraphicalZonotopes.BookSpectrum.HasFullSupportedSummand, hubs, outers, GraphicalZonotopes.BookSpectrum.hubs, GraphicalZonotopes.BookSpectrum.outers, bookUpperIntervalStart, GraphicalZonotopes.BooleanModule.bookUpperIntervalStart, Path.graph, PathJoin.graph, GraphicalZonotopes.Path.graph, GraphicalZonotopes.PathJoin.graph] using
    GraphicalZonotopes.BookSpectrum.prescribed_coordinate_criterion U hU

theorem exponential_family (p : ℕ) (hp : 1≤ p) :
    (twoSingletonGraph p (2^p+p)).CliqueFree 5 ∧
    (∃ Q : Set ((Σ i : Fin 4,Fin (![1,1,p,2^p+p] i))→ℝ),
      LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=2^p+2*p+1 ∧
      IsMinkowskiSummand Q ((((p-1)*2^p+2 : ℕ) : ℝ) •
        graphicalZonotope (twoSingletonGraph p (2^p+p)))) ∧
    ∀ b : ℕ,2^p+p≤ b →
      maximumIndecomposableDimension (twoSingletonGraph p b)=2^p+2*p+1 := by
  simpa only [SetFunction, Supermodular, Normalized, TranslationNormalized, delta, subsetSum, basePolytope, ExtremeSupermodular, MinkowskiIndecomposable, edgeFamily, basisVector, coordinateSimplex, graphicalZonotope, IsMinkowskiSummand, IsWeakMinkowskiSummand, IsExposedSegment, ActualRootEdge, IsFinitePolytope, PolytopalMinkowskiIndecomposable, FullDimension, maximumIndecomposableDimension, IntegerValued, LatticePolytope, Graphical, lowerSupport, BooleanElemental, FullLatticeSummandAt, actualDirectionGraph, cliqueBook, cliqueCapacity, fourPartite, twoSingletonGraph, LeastFullLatticeDilation, GraphicalZonotopes.SetFunction, GraphicalZonotopes.Supermodular, GraphicalZonotopes.Normalized, GraphicalZonotopes.TranslationNormalized, GraphicalZonotopes.delta, GraphicalZonotopes.subsetSum, GraphicalZonotopes.basePolytope, GraphicalZonotopes.ExtremeSupermodular, GraphicalZonotopes.MinkowskiIndecomposable, GraphicalZonotopes.edgeFamily, GraphicalZonotopes.basisVector, GraphicalZonotopes.coordinateSimplex, GraphicalZonotopes.graphicalZonotope, GraphicalZonotopes.IsMinkowskiSummand, GraphicalZonotopes.IsWeakMinkowskiSummand, GraphicalZonotopes.IsExposedSegment, GraphicalZonotopes.ActualRootEdge, GraphicalZonotopes.IsFinitePolytope, GraphicalZonotopes.PolytopalMinkowskiIndecomposable, GraphicalZonotopes.FullDimension, GraphicalZonotopes.maximumIndecomposableDimension, GraphicalZonotopes.IntegerValued, GraphicalZonotopes.LatticePolytope, GraphicalZonotopes.Graphical, GraphicalZonotopes.lowerSupport, GraphicalZonotopes.BooleanElemental, GraphicalZonotopes.FullLatticeSummandAt, GraphicalZonotopes.actualDirectionGraph, GraphicalZonotopes.cliqueBook, GraphicalZonotopes.cliqueCapacity, GraphicalZonotopes.fourPartite, GraphicalZonotopes.twoSingletonGraph, GraphicalZonotopes.LeastFullLatticeDilation, FixesOutside, HasFullSupportedSummand, GraphicalZonotopes.BookSpectrum.FixesOutside, GraphicalZonotopes.BookSpectrum.HasFullSupportedSummand, hubs, outers, GraphicalZonotopes.BookSpectrum.hubs, GraphicalZonotopes.BookSpectrum.outers, bookUpperIntervalStart, GraphicalZonotopes.BooleanModule.bookUpperIntervalStart, Path.graph, PathJoin.graph, GraphicalZonotopes.Path.graph, GraphicalZonotopes.PathJoin.graph] using
    GraphicalZonotopes.TwoHub.exponential_family p hp

theorem corollary_nine_four :
    (∀ m : ℕ,2≤ m → LeastFullLatticeDilation (PathJoin.graph (m-2)) ((m/2 : ℕ) : ℝ)) ∧
    (∀ n : ℕ,4≤ n → LeastFullLatticeDilation (Path.graph n) (if n≤5 then 1 else 2)) := by
  simpa only [SetFunction, Supermodular, Normalized, TranslationNormalized, delta, subsetSum, basePolytope, ExtremeSupermodular, MinkowskiIndecomposable, edgeFamily, basisVector, coordinateSimplex, graphicalZonotope, IsMinkowskiSummand, IsWeakMinkowskiSummand, IsExposedSegment, ActualRootEdge, IsFinitePolytope, PolytopalMinkowskiIndecomposable, FullDimension, maximumIndecomposableDimension, IntegerValued, LatticePolytope, Graphical, lowerSupport, BooleanElemental, FullLatticeSummandAt, actualDirectionGraph, cliqueBook, cliqueCapacity, fourPartite, twoSingletonGraph, LeastFullLatticeDilation, GraphicalZonotopes.SetFunction, GraphicalZonotopes.Supermodular, GraphicalZonotopes.Normalized, GraphicalZonotopes.TranslationNormalized, GraphicalZonotopes.delta, GraphicalZonotopes.subsetSum, GraphicalZonotopes.basePolytope, GraphicalZonotopes.ExtremeSupermodular, GraphicalZonotopes.MinkowskiIndecomposable, GraphicalZonotopes.edgeFamily, GraphicalZonotopes.basisVector, GraphicalZonotopes.coordinateSimplex, GraphicalZonotopes.graphicalZonotope, GraphicalZonotopes.IsMinkowskiSummand, GraphicalZonotopes.IsWeakMinkowskiSummand, GraphicalZonotopes.IsExposedSegment, GraphicalZonotopes.ActualRootEdge, GraphicalZonotopes.IsFinitePolytope, GraphicalZonotopes.PolytopalMinkowskiIndecomposable, GraphicalZonotopes.FullDimension, GraphicalZonotopes.maximumIndecomposableDimension, GraphicalZonotopes.IntegerValued, GraphicalZonotopes.LatticePolytope, GraphicalZonotopes.Graphical, GraphicalZonotopes.lowerSupport, GraphicalZonotopes.BooleanElemental, GraphicalZonotopes.FullLatticeSummandAt, GraphicalZonotopes.actualDirectionGraph, GraphicalZonotopes.cliqueBook, GraphicalZonotopes.cliqueCapacity, GraphicalZonotopes.fourPartite, GraphicalZonotopes.twoSingletonGraph, GraphicalZonotopes.LeastFullLatticeDilation, FixesOutside, HasFullSupportedSummand, GraphicalZonotopes.BookSpectrum.FixesOutside, GraphicalZonotopes.BookSpectrum.HasFullSupportedSummand, hubs, outers, GraphicalZonotopes.BookSpectrum.hubs, GraphicalZonotopes.BookSpectrum.outers, bookUpperIntervalStart, GraphicalZonotopes.BooleanModule.bookUpperIntervalStart, Path.graph, PathJoin.graph, GraphicalZonotopes.Path.graph, GraphicalZonotopes.PathJoin.graph] using
    GraphicalZonotopes.PathJoin.corollary_nine_four

theorem one_singleton_decomposition {I : Type*} [Fintype I] [DecidableEq I]
    (hI : 4 ≤ Fintype.card I) (a : I) :
    ∃ Q R : Set (DoubledParts.SingletonVertices a → ℝ),
      LatticePolytope Q ∧ LatticePolytope R ∧ MinkowskiIndecomposable Q ∧
      MinkowskiIndecomposable R ∧ FullDimension Q ∧ FullDimension R ∧
      Q + R = graphicalZonotope (DoubledParts.singletonGraph a) ∧
      actualDirectionGraph Q = DoubledParts.singletonGraph a ∧
      actualDirectionGraph R = DoubledParts.singletonGraph a ∧
      BooleanElemental Q ∧ BooleanElemental R := by
  refine ⟨GraphicalZonotopes.DoubledParts.singletonPolytope a,
    GraphicalZonotopes.DoubledParts.singletonComplementPolytope a, ?_⟩
  simpa only [SetFunction, Supermodular, Normalized, TranslationNormalized, delta, subsetSum, basePolytope, ExtremeSupermodular, MinkowskiIndecomposable, edgeFamily, basisVector, coordinateSimplex, graphicalZonotope, IsMinkowskiSummand, IsWeakMinkowskiSummand, IsExposedSegment, ActualRootEdge, IsFinitePolytope, PolytopalMinkowskiIndecomposable, FullDimension, maximumIndecomposableDimension, IntegerValued, LatticePolytope, Graphical, lowerSupport, BooleanElemental, FullLatticeSummandAt, actualDirectionGraph, cliqueBook, cliqueCapacity, fourPartite, twoSingletonGraph, LeastFullLatticeDilation, GraphicalZonotopes.SetFunction, GraphicalZonotopes.Supermodular, GraphicalZonotopes.Normalized, GraphicalZonotopes.TranslationNormalized, GraphicalZonotopes.delta, GraphicalZonotopes.subsetSum, GraphicalZonotopes.basePolytope, GraphicalZonotopes.ExtremeSupermodular, GraphicalZonotopes.MinkowskiIndecomposable, GraphicalZonotopes.edgeFamily, GraphicalZonotopes.basisVector, GraphicalZonotopes.coordinateSimplex, GraphicalZonotopes.graphicalZonotope, GraphicalZonotopes.IsMinkowskiSummand, GraphicalZonotopes.IsWeakMinkowskiSummand, GraphicalZonotopes.IsExposedSegment, GraphicalZonotopes.ActualRootEdge, GraphicalZonotopes.IsFinitePolytope, GraphicalZonotopes.PolytopalMinkowskiIndecomposable, GraphicalZonotopes.FullDimension, GraphicalZonotopes.maximumIndecomposableDimension, GraphicalZonotopes.IntegerValued, GraphicalZonotopes.LatticePolytope, GraphicalZonotopes.Graphical, GraphicalZonotopes.lowerSupport, GraphicalZonotopes.BooleanElemental, GraphicalZonotopes.FullLatticeSummandAt, GraphicalZonotopes.actualDirectionGraph, GraphicalZonotopes.cliqueBook, GraphicalZonotopes.cliqueCapacity, GraphicalZonotopes.fourPartite, GraphicalZonotopes.twoSingletonGraph, GraphicalZonotopes.LeastFullLatticeDilation, FixesOutside, HasFullSupportedSummand, GraphicalZonotopes.BookSpectrum.FixesOutside, GraphicalZonotopes.BookSpectrum.HasFullSupportedSummand, hubs, outers, GraphicalZonotopes.BookSpectrum.hubs, GraphicalZonotopes.BookSpectrum.outers, bookUpperIntervalStart, GraphicalZonotopes.BooleanModule.bookUpperIntervalStart, Path.graph, PathJoin.graph, GraphicalZonotopes.Path.graph, GraphicalZonotopes.PathJoin.graph, DoubledParts.singletonGraph, GraphicalZonotopes.DoubledParts.singletonGraph, GraphicalZonotopes.DoubledParts.graph, GraphicalZonotopes.VertexDeletion.embedding] using
    GraphicalZonotopes.DoubledParts.one_singleton_decomposition hI a

theorem four_small_parts_decomposition :
  ∀ a : Fin 4 → ℕ, (∀ i, a i = 1 ∨ a i = 2) →
    ∃ Q R : Set ((Σ i : Fin 4, Fin (a i)) → ℝ),
      LatticePolytope Q ∧ LatticePolytope R ∧
      MinkowskiIndecomposable Q ∧ MinkowskiIndecomposable R ∧
      FullDimension Q ∧ FullDimension R ∧ Q+R = graphicalZonotope (fourPartite a) ∧
      actualDirectionGraph Q = fourPartite a ∧ actualDirectionGraph R = fourPartite a ∧
      BooleanElemental Q ∧ BooleanElemental R := by
  simpa only [GraphicalZonotopes.Targets.FourSmallPartsDecomposition, SetFunction, Supermodular, Normalized, TranslationNormalized, delta, subsetSum, basePolytope, ExtremeSupermodular, MinkowskiIndecomposable, edgeFamily, basisVector, coordinateSimplex, graphicalZonotope, IsMinkowskiSummand, IsWeakMinkowskiSummand, IsExposedSegment, ActualRootEdge, IsFinitePolytope, PolytopalMinkowskiIndecomposable, FullDimension, maximumIndecomposableDimension, IntegerValued, LatticePolytope, Graphical, lowerSupport, BooleanElemental, FullLatticeSummandAt, actualDirectionGraph, cliqueBook, cliqueCapacity, fourPartite, twoSingletonGraph, LeastFullLatticeDilation, GraphicalZonotopes.SetFunction, GraphicalZonotopes.Supermodular, GraphicalZonotopes.Normalized, GraphicalZonotopes.TranslationNormalized, GraphicalZonotopes.delta, GraphicalZonotopes.subsetSum, GraphicalZonotopes.basePolytope, GraphicalZonotopes.ExtremeSupermodular, GraphicalZonotopes.MinkowskiIndecomposable, GraphicalZonotopes.edgeFamily, GraphicalZonotopes.basisVector, GraphicalZonotopes.coordinateSimplex, GraphicalZonotopes.graphicalZonotope, GraphicalZonotopes.IsMinkowskiSummand, GraphicalZonotopes.IsWeakMinkowskiSummand, GraphicalZonotopes.IsExposedSegment, GraphicalZonotopes.ActualRootEdge, GraphicalZonotopes.IsFinitePolytope, GraphicalZonotopes.PolytopalMinkowskiIndecomposable, GraphicalZonotopes.FullDimension, GraphicalZonotopes.maximumIndecomposableDimension, GraphicalZonotopes.IntegerValued, GraphicalZonotopes.LatticePolytope, GraphicalZonotopes.Graphical, GraphicalZonotopes.lowerSupport, GraphicalZonotopes.BooleanElemental, GraphicalZonotopes.FullLatticeSummandAt, GraphicalZonotopes.actualDirectionGraph, GraphicalZonotopes.cliqueBook, GraphicalZonotopes.cliqueCapacity, GraphicalZonotopes.fourPartite, GraphicalZonotopes.twoSingletonGraph, GraphicalZonotopes.LeastFullLatticeDilation, FixesOutside, HasFullSupportedSummand, GraphicalZonotopes.BookSpectrum.FixesOutside, GraphicalZonotopes.BookSpectrum.HasFullSupportedSummand, hubs, outers, GraphicalZonotopes.BookSpectrum.hubs, GraphicalZonotopes.BookSpectrum.outers, bookUpperIntervalStart, GraphicalZonotopes.BooleanModule.bookUpperIntervalStart, Path.graph, PathJoin.graph, GraphicalZonotopes.Path.graph, GraphicalZonotopes.PathJoin.graph] using
    GraphicalZonotopes.FourSmallParts.four_small_parts_decomposition

/-- The unbounded final clause of Corollary9.11. -/
theorem boolean_decomposition_every_dimension {d : ℕ} (hd : 3≤ d) :
    ∃ G : SimpleGraph (Fin (d+1)),∃ Q R : Set (Fin (d+1) → ℝ),
      LatticePolytope Q ∧ LatticePolytope R ∧
      MinkowskiIndecomposable Q ∧ MinkowskiIndecomposable R ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=d ∧ Module.finrank ℝ (vectorSpan ℝ R)=d ∧
      Q+R=graphicalZonotope G ∧ BooleanElemental Q ∧ BooleanElemental R := by
  exact GraphicalZonotopes.boolean_decomposition_every_dimension hd

end PalomarGraphicalConsequences
