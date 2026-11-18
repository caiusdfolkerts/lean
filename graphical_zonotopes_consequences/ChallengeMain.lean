module
public import Mathlib
/-!
# Principal graphical-zonotope geometry and classification

Independent literal definitions of genuine convex bodies, Minkowski sums,
exposed directions, ordinary 3-trees and fixed integer lattices. Every
constructor proof is genuine. Only named theorem obligations are holes;
all those names are selected for comparison. The Solution proves the fresh
statements from the preserved source, using a proved constructor-induction
bridge for the independently defined 3-tree relation.
-/
@[expose] public section
noncomputable section
open Set Finset
open scoped BigOperators Pointwise Classical
namespace PalomarGraphicalMain
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Real functions on subsets of the fixed finite ground set. -/
abbrev SetFunction (V : Type*) := Finset V → ℝ
/-- Ordinary supermodularity. -/
def Supermodular (z : SetFunction V) : Prop :=
  ∀ A B, z A + z B ≤ z (A ∪ B) + z (A ∩ B)
/-- Vanishing value on the empty set. -/
def Normalized (z : SetFunction V) : Prop := z ∅ = 0
/-- Remove both constant and singleton translation data. -/
def TranslationNormalized (z : SetFunction V) : Prop :=
  Normalized z ∧ ∀ v, z {v} = 0
/-- The elemental supermodular difference. -/
def delta (z : SetFunction V) (u v : V) (S : Finset V) : ℝ :=
  z (insert u (insert v S)) - z (insert u S) - z (insert v S) + z S
/-- Sum the specified standard coordinates. -/
def subsetSum (x : V → ℝ) (S : Finset V) : ℝ := ∑ v ∈ S, x v
/-- The genuine lower base polytope cut out by every subset inequality. -/
def basePolytope (z : SetFunction V) : Set (V → ℝ) :=
  {x | subsetSum x univ = z univ ∧ ∀ S, z S ≤ subsetSum x S}
/-- Extremality in the normalized supermodular cone by its actual decomposition property. -/
def ExtremeSupermodular (z : SetFunction V) : Prop :=
  TranslationNormalized z ∧ Supermodular z ∧ z ≠ 0 ∧
    ∀ f g : SetFunction V,
      TranslationNormalized f → TranslationNormalized g →
      Supermodular f → Supermodular g → f + g = z →
      ∃ a : ℝ, 0 ≤ a ∧ f = a • z
/-- Indecomposability against arbitrary compact convex Minkowski summands. -/
def MinkowskiIndecomposable (Q : Set (V → ℝ)) : Prop :=
  Q.Nonempty ∧ ∀ P R : Set (V → ℝ),
    IsCompact P → IsCompact R → Convex ℝ P → Convex ℝ R →
    P + R = Q → ∃ (a : ℝ) (t : V → ℝ), 0 ≤ a ∧ P = ({t} : Set (V → ℝ)) + a • Q
/-- The zeta transform on the ordinary subset lattice. -/
def zeta (y : SetFunction V) : SetFunction V := fun S => ∑ C ∈ S.powerset, y C
/-- The zeta transform as a linear map. -/
theorem zeta_add (y z : SetFunction V) : zeta (y+z) = zeta y+zeta z := by
  funext S
  simp [zeta, sum_add_distrib]
theorem zeta_smul (a : ℝ) (y : SetFunction V) : zeta (a • y) = a • zeta y := by
  funext S
  simp [zeta, mul_sum]
def zetaLinear : SetFunction V →ₗ[ℝ] SetFunction V where
  toFun := zeta
  map_add' := zeta_add
  map_smul' := zeta_smul
/-- The finite subset zeta transform is injective. -/
theorem zeta_injective : Function.Injective (zeta : SetFunction V → SetFunction V) := by sorry
/-- The invertible ordinary subset zeta transform. -/
def zetaEquiv : SetFunction V ≃ₗ[ℝ] SetFunction V :=
  LinearEquiv.ofInjectiveEndo zetaLinear zeta_injective
/-- Ordinary Mobius coefficients, the inverse of subset summation. -/
def mobius (z : SetFunction V) : SetFunction V := zetaEquiv.symm z
/-- The unordered two-element actual edges of a simple graph. -/
def edgeFamily (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact univ.filter (fun C => C.card = 2 ∧ ∀ u ∈ C, ∀ v ∈ C, u ≠ v → G.Adj u v)
/-- The clique graph on a finite set, with all other vertices isolated. -/
def cliqueGraph (C : Finset V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ u ∈ C ∧ v ∈ C
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
/-- Edges from a new vertex to exactly the specified triangle. -/
def attachmentStar (u : V) (T : Finset V) : SimpleGraph V where
  Adj v w := v ≠ w ∧ ((v = u ∧ w ∈ T) ∨ (w = u ∧ v ∈ T))
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
/-- The usual recursive 3-tree construction on its entire active vertex set. -/
inductive ThreeTreeOn : Finset V → SimpleGraph V → Prop
  | tetrahedron (C : Finset V) (hC : C.card = 4) : ThreeTreeOn C (cliqueGraph C)
  | attach {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
      (u : V) (hu : u ∉ S) (T : Finset V) (hT : T.card = 3)
      (hTS : T ⊆ S) (hcl : G.IsClique T) :
      ThreeTreeOn (insert u S) (G ⊔ attachmentStar u T)
/-- A 3-tree on the complete specified ground set. -/
def IsThreeTree (G : SimpleGraph V) : Prop := ThreeTreeOn univ G
/-- The four-cliques of a graph. -/
def tetrahedra (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact univ.filter (fun C => C.card = 4 ∧ G.IsClique C)
/-- Number of four-cliques containing a given triangle. -/
def triangleMultiplicity (G : SimpleGraph V) (T : Finset V) : ℕ := by
  classical
  exact ((tetrahedra G).filter (fun C => T ⊆ C)).card
/-- Every triangle belongs to at most three four-cliques. -/
def Admissible (G : SimpleGraph V) : Prop :=
  ∀ T : Finset V, T.card = 3 → G.IsClique T → triangleMultiplicity G T ≤ 3
/-- The standard coordinate basis vector. -/
def basisVector (v : V) : V → ℝ := Pi.single v 1
/-- The coordinate simplex on the specified labels. -/
def coordinateSimplex (C : Finset V) : Set (V → ℝ) :=
  convexHull ℝ (basisVector '' (C : Set V))
/-- Actual Minkowski sum of all standard-basis edge segments of the graph. -/
def graphicalZonotope (G : SimpleGraph V) : Set (V → ℝ) :=
  ∑ C ∈ edgeFamily G, coordinateSimplex C
/-- A compact convex complementary summand in a literal Minkowski equality. -/
def IsMinkowskiSummand (Q Z : Set (V → ℝ)) : Prop :=
  ∃ R : Set (V → ℝ), IsCompact R ∧ Convex ℝ R ∧ R.Nonempty ∧ Q+R=Z
/-- A summand after multiplying the target by a positive real dilation. -/
def IsWeakMinkowskiSummand (Q Z : Set (V → ℝ)) : Prop :=
  ∃ a : ℝ, 0< a ∧ IsMinkowskiSummand Q (a • Z)
/-- A nondegenerate exposed one-dimensional face, with a genuine linear support. -/
def IsExposedSegment (Q : Set (V → ℝ)) (p q : V → ℝ) : Prop :=
  p ≠ q ∧ ∃ ℓ : (V → ℝ) →ₗ[ℝ] ℝ, ∃ a : ℝ,
    (∀ x ∈ Q, a ≤ ℓ x) ∧ {x ∈ Q | ℓ x = a} = segment ℝ p q
/-- An actual exposed edge parallel to the specified standard root. -/
def ActualRootEdge (Q : Set (V → ℝ)) (u v : V) : Prop :=
  u ≠ v ∧ ∃ p q, IsExposedSegment Q p q ∧
    ∃ a : ℝ, a ≠ 0 ∧ q-p = a • (basisVector u-basisVector v)
/-- Finite convex hull in the actual standard coordinate space. -/
def IsFinitePolytope (Q : Set (V → ℝ)) : Prop :=
  ∃ s : Finset (V → ℝ), convexHull ℝ (s : Set (V → ℝ)) = Q
/-- Ordinary generalized permutahedron as a lower base polytope. -/
def IsGeneralizedPermutahedron (Q : Set (V → ℝ)) : Prop :=
  ∃ z : SetFunction V, Normalized z ∧ Supermodular z ∧ Q = basePolytope z
/-- The traditional indecomposability condition over actual finite polytopes. -/
def PolytopalMinkowskiIndecomposable (Q : Set (V → ℝ)) : Prop :=
  Q.Nonempty ∧ ∀ P R : Set (V → ℝ),IsFinitePolytope P → IsFinitePolytope R →
    P+R=Q → ∃ (a : ℝ) (t : V → ℝ),0≤ a ∧ P=({t} : Set (V → ℝ))+a • Q
/-- Symmetry of actual standard-root directions. -/
theorem actualRootEdge_symm {Q : Set (V → ℝ)} {u v : V}
    (h : ActualRootEdge Q u v) : ActualRootEdge Q v u := by sorry
/-- The actual geometric direction graph, excluding all unrealized roots. -/
def actualDirectionGraph (Q : Set (V → ℝ)) : SimpleGraph V where
  Adj := ActualRootEdge Q
  symm := ⟨fun _ _ => actualRootEdge_symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
/-- The actual number of distinct standard-root directions. -/
def directionCount (Q : Set (V → ℝ)) : ℕ := (edgeFamily (actualDirectionGraph Q)).card
/-- Maximum degree of the actual direction graph. -/
def maximumDirectionDegree (Q : Set (V → ℝ)) : ℕ := by
  classical
  exact (actualDirectionGraph Q).maxDegree
/-- Full affine dimension n-1 in the coordinate-sum hyperplane. -/
def FullDimension (Q : Set (V → ℝ)) : Prop :=
  Module.finrank ℝ (vectorSpan ℝ Q) = Fintype.card V - 1
/-- Integer-valued subset data in the fixed lattice. -/
def IntegerValued (z : SetFunction V) : Prop := ∀ S, ∃ a : ℤ, z S = (a : ℝ)
/-- Convex hull of finitely many standard integer coordinate vectors. -/
def LatticePolytope (Q : Set (V → ℝ)) : Prop :=
  ∃ P : Finset (V → ℤ), Q = convexHull ℝ ((fun x : V → ℤ => fun v => (x v : ℝ)) '' (P : Set (V → ℤ)))
/-- A concrete plane embedding by straight segments with no unwanted intersections. -/
def HasPlaneStraightLineDrawing {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ p : V → (Fin 2 → ℝ), Function.Injective p ∧
    (∀ u v w, G.Adj u v → w ≠ u → w ≠ v →
      p w ∉ segment ℝ (p u) (p v)) ∧
    ∀ u v a b, G.Adj u v → G.Adj a b → ∀ x : Fin 2 → ℝ,
      x ∈ segment ℝ (p u) (p v) → x ∈ segment ℝ (p a) (p b) →
      (u = a ∧ v = b) ∨ (u = b ∧ v = a) ∨
        ∃ w, (w = u ∨ w = v) ∧ (w = a ∨ w = b) ∧ x = p w
namespace Path
/-- The third power of the path on the literal labels 0,...,n-1. -/
def graph (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ u.val ≤ v.val + 3 ∧ v.val ≤ u.val + 3
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
end Path




/-- Full-dimensional indecomposable weak summand in the actual coordinate space. -/
def SupportsFullIndecomposable (G : SimpleGraph V) : Prop :=
  ∃ Q : Set (V → ℝ), IsFinitePolytope Q ∧ MinkowskiIndecomposable Q ∧
    FullDimension Q ∧ IsWeakMinkowskiSummand Q (graphicalZonotope G)
/-- Maximum dimension over actual finite indecomposable weak summands. -/
def maximumIndecomposableDimension (G : SimpleGraph V) : ℕ :=
  sSup {d : ℕ | ∃ Q : Set (V → ℝ), IsFinitePolytope Q ∧
    MinkowskiIndecomposable Q ∧ IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
    Module.finrank ℝ (vectorSpan ℝ Q) = d}
/-- Maximum dimension when the actual active direction graph is a 3-tree. -/
def maximumThreeTreeSupportDimension (G : SimpleGraph V) : ℕ :=
  sSup {d : ℕ | ∃ Q : Set (V → ℝ), IsFinitePolytope Q ∧
    MinkowskiIndecomposable Q ∧ IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
    (∃ S : Finset V, ThreeTreeOn S (actualDirectionGraph Q)) ∧
    Module.finrank ℝ (vectorSpan ℝ Q) = d}
/-- Admissible spanning 3-tree in the ordinary graph order. -/
def HasAdmissibleSpanningThreeTree (G : SimpleGraph V) : Prop :=
  ∃ H : SimpleGraph V, H ≤ G ∧ IsThreeTree H ∧ Admissible H
/-- Join of an s-clique and k isolated vertices. -/
def cliqueBook (s k : ℕ) : SimpleGraph (Fin s ⊕ Fin k) where
  Adj u v := u ≠ v ∧ (u.isLeft ∨ v.isLeft)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
/-- The exact clique-separator capacity. -/
def cliqueCapacity (s : ℕ) : ℕ :=
  s.choose 2 * 2^(s-2) - (2^s-s-1) + 1
/-- The exact minimum number of neighbors of a saturated-book hub. -/
def saturatedHubNeighbors (s : ℕ) : ℕ :=
  if s = 2 then 1 else cliqueCapacity s - cliqueCapacity (s-1) + 1
/-- Complete four-partite graph with the specified literal part sizes. -/
def fourPartite (a : Fin 4 → ℕ) : SimpleGraph (Σ i : Fin 4, Fin (a i)) :=
  SimpleGraph.completeMultipartiteGraph (fun i => Fin (a i))
/-- Complete four-partite graph with two singleton parts. -/
def twoSingletonGraph (p b : ℕ) := fourPartite ![1,1,p,b]
/-- Complete multipartite graph with r parts each of size two. -/
def doubledPartGraph (r : ℕ) : SimpleGraph (Fin r × Fin 2) where
  Adj u v := u.1 ≠ v.1
  symm := ⟨fun _ _ => Ne.symm⟩
  loopless := ⟨fun _ h => h rfl⟩
/-- Minimum of a coordinate sum on the actual convex body. -/
def lowerSupport (P : Set (V → ℝ)) (S : Finset V) : ℝ :=
  sInf ((fun x => subsetSum x S) '' P)
/-- Deleting any actual edge destroys full indecomposable support. -/
def EdgeMinimalSupporting (G : SimpleGraph V) : Prop :=
  SupportsFullIndecomposable G ∧
    ∀ H : SimpleGraph V, H < G → ¬SupportsFullIndecomposable H
/-- Every actual lower-support elemental slack is zero or one. -/
def BooleanElemental (Q : Set (V → ℝ)) : Prop :=
  ∀ u v, u ≠ v → ∀ S : Finset V, u ∉ S → v ∉ S →
    delta (lowerSupport Q) u v S = 0 ∨ delta (lowerSupport Q) u v S = 1
/-- Central symmetry up to an actual coordinate translation. -/
def CentrallySymmetricUpToTranslation (Q : Set (V → ℝ)) : Prop :=
  ∃ t : V → ℝ, Q = ({t} : Set (V → ℝ)) + (-1 : ℝ) • Q
/-- A full-dimensional lattice indecomposable actual summand at the stated dilation. -/
def FullLatticeSummandAt (G : SimpleGraph V) (a : ℝ) : Prop :=
  ∃ Q : Set (V → ℝ), LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
    FullDimension Q ∧ IsMinkowskiSummand Q (a • graphicalZonotope G)
/-- Standard finite tree decomposition, with coverage and connected bag occurrences. -/
def HasTreewidthAtMost (G : SimpleGraph V) (w : ℕ) : Prop :=
  ∃ m : ℕ, ∃ T : SimpleGraph (Fin m), ∃ bag : Fin m → Finset V,
    T.IsTree ∧ (∀ i, (bag i).card ≤ w+1) ∧
    (∀ v, ∃ i, v ∈ bag i) ∧
    (∀ u v, G.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i) ∧
    ∀ v, (T.induce {i | v ∈ bag i}).Connected
end PalomarGraphicalMain
namespace PalomarGraphicalMain
/-- The corresponding complete principal theorem, with every original hypothesis. -/
theorem direction_bounds_polytopal (n : ℕ) (hn : 4≤ n) (Q : Set (Fin n → ℝ))
    (hQ : IsGeneralizedPermutahedron Q) (hi : PolytopalMinkowskiIndecomposable Q)
    (hd : FullDimension Q) :
    3*n-6≤ directionCount Q ∧ min (n-1) 6≤ maximumDirectionDegree Q ∧
    (directionCount Q=3*n-6 → IsThreeTree (actualDirectionGraph Q)) := by sorry
/-- The corresponding complete principal theorem, with every original hypothesis. -/
theorem threeTree_classification_polytopal {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G) :
    ((∃ Q : Set (Fin n → ℝ), IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G)) ↔
      ∀ T : Finset (Fin n),T.card=3 → G.IsClique T →
        (univ.filter (fun C : Finset (Fin n) => C.card=4 ∧
          Maximal G.IsClique (C : Set (Fin n)) ∧ T⊆C)).card≤3) ∧
    ((∃ Q : Set (Fin n → ℝ), IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope G)) ↔
      ∀ T : Finset (Fin n),T.card=3 → G.IsClique T →
        Nat.card (G.induce ((T : Set (Fin n))ᶜ)).ConnectedComponent≤3) := by sorry
/-- The corresponding complete principal theorem, with every original hypothesis. -/
theorem admissible_threeTree_lattice_witness {n : ℕ} (hn : 4≤ n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G) (hA : Admissible G) :
    ∃ z : SetFunction (Fin n),ExtremeSupermodular z ∧ IntegerValued (mobius z) ∧
      LatticePolytope (basePolytope z) ∧ MinkowskiIndecomposable (basePolytope z) ∧
      FullDimension (basePolytope z) ∧ actualDirectionGraph (basePolytope z)=G ∧
      (∀ C : Finset (Fin n),Maximal G.IsClique (C : Set (Fin n)) → mobius z C=1) ∧
      (∀ T : Finset (Fin n),T.card=3 → G.IsClique T →
        mobius z T=0 ∨ mobius z T= -1 ∨ mobius z T= -2) ∧
      IsMinkowskiSummand (basePolytope z) (((n-3 : ℕ) : ℝ) • graphicalZonotope G) := by sorry
namespace Targets
def DirectionBounds : Prop :=
  ∀ n : ℕ, 4 ≤ n → ∀ Q : Set (Fin n → ℝ),
    IsGeneralizedPermutahedron Q → MinkowskiIndecomposable Q → FullDimension Q →
    3*n-6 ≤ directionCount Q ∧ min (n-1) 6 ≤ maximumDirectionDegree Q ∧
    (directionCount Q = 3*n-6 → IsThreeTree (actualDirectionGraph Q))

/-- The equivalence and the complete quantitative construction in Theorem6.1.
All tetrahedra of a 3-tree are maximal cliques. -/
def ThreeTreeClassification : Prop :=
  ∀ n : ℕ, 4 ≤ n → ∀ G : SimpleGraph (Fin n), IsThreeTree G →
    (SupportsFullIndecomposable G ↔ Admissible G) ∧
    (Admissible G ↔ ∀ T : Finset (Fin n), T.card = 3 → G.IsClique T →
      Nat.card ((G.induce ((T : Set (Fin n))ᶜ)).ConnectedComponent) ≤ 3) ∧
    (Admissible G → ∃ z : SetFunction (Fin n), ExtremeSupermodular z ∧
      IntegerValued (mobius z) ∧
      (∀ C ∈ tetrahedra G, mobius z C = 1) ∧
      (∀ T : Finset (Fin n), T.card = 3 → G.IsClique T →
        mobius z T = 0 ∨ mobius z T = -1 ∨ mobius z T = -2) ∧
      FullDimension (basePolytope z) ∧ actualDirectionGraph (basePolytope z) = G ∧
      IsMinkowskiSummand (basePolytope z) (((n-3 : ℕ) : ℝ) • graphicalZonotope G))

/-- Theorem7.1, including attainment in the stated lattice dilation. -/
def CliqueBookClassification : Prop :=
  ∀ s k : ℕ, 2 ≤ s → 1 ≤ k →
    maximumIndecomposableDimension (cliqueBook s k) =
      min (s+k-1) (s+cliqueCapacity s-1) ∧
    (SupportsFullIndecomposable (cliqueBook s k) ↔ k ≤ cliqueCapacity s) ∧
    ∃ Q : Set ((Fin s ⊕ Fin k) → ℝ), LatticePolytope Q ∧
      MinkowskiIndecomposable Q ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = min (s+k-1) (s+cliqueCapacity s-1) ∧
      IsMinkowskiSummand Q ((((s-1)*min k (cliqueCapacity s) : ℕ) : ℝ) •
        graphicalZonotope (cliqueBook s k))

/-- Theorem7.12. The quantified lower bound and the lattice equality witness
are stated together, so the word "minimum" conceals no attainment premise. -/
def SaturatedBookDirections : Prop :=
  ∀ s : ℕ, 2 ≤ s →
    (∀ Q : Set ((Fin s ⊕ Fin (cliqueCapacity s)) → ℝ),
      IsFinitePolytope Q → MinkowskiIndecomposable Q → FullDimension Q →
      IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s (cliqueCapacity s))) →
      s.choose 2+s*saturatedHubNeighbors s ≤ directionCount Q ∧
      (3 ≤ s → ∀ i j : Fin s, i ≠ j →
        ActualRootEdge Q (Sum.inl i) (Sum.inl j)) ∧
      ∀ i : Fin s, saturatedHubNeighbors s ≤
        (univ.filter (fun j : Fin (cliqueCapacity s) =>
          ActualRootEdge Q (Sum.inl i) (Sum.inr j))).card) ∧
    ∃ Q : Set ((Fin s ⊕ Fin (cliqueCapacity s)) → ℝ),
      LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s (cliqueCapacity s))) ∧
      directionCount Q = s.choose 2+s*saturatedHubNeighbors s ∧
      ∀ i : Fin s, (univ.filter (fun j : Fin (cliqueCapacity s) =>
        ActualRootEdge Q (Sum.inl i) (Sum.inr j))).card = saturatedHubNeighbors s

/-- Theorem8.1, including its extremal six-branch witness. -/
def DiamondBookClassification : Prop :=
  (∀ k : ℕ, 1 ≤ k →
    maximumIndecomposableDimension (twoSingletonGraph 2 k) = min (k+3) 9) ∧
  ∃ Q : Set ((Σ i : Fin 4, Fin (![1,1,2,6] i)) → ℝ),
    LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧ FullDimension Q ∧
    IsMinkowskiSummand Q ((4 : ℝ) • graphicalZonotope (twoSingletonGraph 2 6)) ∧
    directionCount Q = 25 ∧
    ¬HasAdmissibleSpanningThreeTree (twoSingletonGraph 2 6)

/-- Theorem8.2. "Treewidth four" means width at most four and not at most
three, with the standard tree-decomposition definition above. -/
def SparseTreewidthFourFamily : Prop :=
  ∀ n : ℕ, 10 ≤ n → ∃ G : SimpleGraph (Fin n),
    G.CliqueFree 5 ∧ (edgeFamily G).card = 3*n-5 ∧
    HasTreewidthAtMost G 4 ∧ ¬HasTreewidthAtMost G 3 ∧
    EdgeMinimalSupporting G ∧ FullLatticeSummandAt G (n-6 : ℕ)

/-- Theorem8.7, together with lattice attainment of the exact dimension. -/
def TwoSingletonClassification : Prop :=
  ∀ p b : ℕ, 1 ≤ p → 1 ≤ b →
    maximumIndecomposableDimension (twoSingletonGraph p b) =
      min (p+b+1) (2^(min p b)+2*min p b+1) ∧
    (SupportsFullIndecomposable (twoSingletonGraph p b) ↔
      max p b ≤ 2^(min p b)+min p b) ∧
    ∃ Q : Set ((Σ i : Fin 4, Fin (![1,1,p,b] i)) → ℝ),
      LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (twoSingletonGraph p b)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = min (p+b+1) (2^(min p b)+2*min p b+1)

/-- Theorem8.9. The second invariant explicitly restricts the actual
direction support to a 3-tree on its active vertices. -/
def FourPartiteSpanningThreeTrees : Prop :=
  ∀ a : Fin 4 → ℕ, (∀ i, 1 ≤ a i) →
    (HasAdmissibleSpanningThreeTree (fourPartite a) ↔
      3*(univ.sup a) ≤ 2*(∑ i, a i)-3) ∧
    maximumThreeTreeSupportDimension (fourPartite a) =
      min ((∑ i, a i)-1) (3*((∑ i, a i)-univ.sup a)-4)

/-- Theorem9.1, including every nonzero integral tetrahedral coefficient and
the complete edgewise integer-ceiling lower bound. -/
def ThreeTreeLatticeDilation : Prop :=
  (∀ n : ℕ, 6 ≤ n → ∀ G : SimpleGraph (Fin n), IsThreeTree G →
    ∀ Q : Set (Fin n → ℝ), LatticePolytope Q → MinkowskiIndecomposable Q →
      FullDimension Q → ∀ a : ℝ, 0 < a →
      IsMinkowskiSummand Q (a • graphicalZonotope G) →
      2 ≤ a ∧
      (∀ C ∈ tetrahedra G, ∃ k : ℤ, k ≠ 0 ∧ mobius (lowerSupport Q) C = k) ∧
      ∀ e ∈ edgeFamily G,
        ((Int.ceil ((1/2 : ℝ) *
          ∑ C ∈ (tetrahedra G).filter (fun C => e ⊆ C),
            |mobius (lowerSupport Q) C|)) : ℝ) ≤ a) ∧
  ∀ n : ℕ, 6 ≤ n → FullLatticeSummandAt (Path.graph n) 2

/-- Theorem9.5, with the ambient graph conclusion and all actual directions. -/
def UnitLatticeClassification : Prop :=
  ∀ n : ℕ, 4 ≤ n → ∀ G : SimpleGraph (Fin n), G.CliqueFree 5 →
    ∀ Q : Set (Fin n → ℝ), LatticePolytope Q → MinkowskiIndecomposable Q →
      FullDimension Q → IsMinkowskiSummand Q (graphicalZonotope G) →
      actualDirectionGraph Q = G ∧ n ≤ 8 ∧
      ∃ a : Fin 4 → ℕ, (∀ i, a i = 1 ∨ a i = 2) ∧ Nonempty (G ≃g fourPartite a)

/-- Theorem9.8, including both indecomposabilities, all dimensions, all
directions, Boolean slacks and the parity-dependent symmetry conclusions. -/
def DoubledPartsBooleanPhases : Prop :=
  ∀ r : ℕ, 4 ≤ r → ∃ Q R : Set ((Fin r × Fin 2) → ℝ),
    LatticePolytope Q ∧ LatticePolytope R ∧
    MinkowskiIndecomposable Q ∧ MinkowskiIndecomposable R ∧
    FullDimension Q ∧ FullDimension R ∧
    Q+R = graphicalZonotope (doubledPartGraph r) ∧
    actualDirectionGraph Q = doubledPartGraph r ∧
    actualDirectionGraph R = doubledPartGraph r ∧
    BooleanElemental Q ∧ BooleanElemental R ∧
    (Even r → CentrallySymmetricUpToTranslation Q ∧ CentrallySymmetricUpToTranslation R) ∧
    (Odd r → ∃ t, R = ({t} : Set ((Fin r × Fin 2) → ℝ)) + (-1 : ℝ) • Q) ∧
    (Odd r → graphicalZonotope (doubledPartGraph r) =
      Q+(-1 : ℝ) • Q+({fun _ : Fin r × Fin 2 => ((r-1 : ℕ) : ℝ)} : Set ((Fin r × Fin 2) → ℝ)))

/-- Corollary9.12, expressed as both attainment and a universal lower bound
over every K5-free graph on exactly n vertices. -/
def OptimalK5FreeDilation : Prop :=
  ∀ n : ℕ, 4 ≤ n →
    (∃ G : SimpleGraph (Fin n), G.CliqueFree 5 ∧
      FullLatticeSummandAt G (if n ≤ 8 then 1 else 2)) ∧
    ∀ G : SimpleGraph (Fin n), G.CliqueFree 5 → ∀ a : ℝ,
      0 < a → FullLatticeSummandAt G a → (if n ≤ 8 then 1 else 2) ≤ a

end Targets

/-- Complete corresponding principal theorem, including its quantitative witness. -/
theorem clique_book_classification : Targets.CliqueBookClassification := by sorry

/-- Complete corresponding principal theorem, including its quantitative witness. -/
theorem SaturatedDirections.paper_theorem_7_12 :
    ∀ s : ℕ,2 ≤ s →
      (∀ Q : Set ((Fin s ⊕ Fin (cliqueCapacity s)) → ℝ),
        IsFinitePolytope Q → MinkowskiIndecomposable Q → FullDimension Q →
        IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s (cliqueCapacity s))) →
        s.choose 2 + s*saturatedHubNeighbors s ≤ directionCount Q ∧
        (3 ≤ s → ∀ i j : Fin s,i ≠ j → ActualRootEdge Q (Sum.inl i) (Sum.inl j)) ∧
        ∀ i : Fin s,saturatedHubNeighbors s ≤
          (univ.filter (fun j : Fin (cliqueCapacity s) =>
            ActualRootEdge Q (Sum.inl i) (Sum.inr j))).card) ∧
      ∃ Q : Set ((Fin s ⊕ Fin (cliqueCapacity s)) → ℝ),
        LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧ FullDimension Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s (cliqueCapacity s))) ∧
        directionCount Q = s.choose 2 + s*saturatedHubNeighbors s ∧
        ∀ i : Fin s,(univ.filter (fun j : Fin (cliqueCapacity s) =>
          ActualRootEdge Q (Sum.inl i) (Sum.inr j))).card = saturatedHubNeighbors s := by sorry

/-- Complete corresponding principal theorem, including its quantitative witness. -/
theorem DiamondBook.paper_theorem_8_1 : Targets.DiamondBookClassification := by sorry

/-- Complete corresponding principal theorem, including its quantitative witness. -/
theorem SparseFamily.paper_theorem_8_2_polytopal (n : ℕ) (hn : 10 ≤ n) :
    ∃ G : SimpleGraph (Fin n), ∃ Q : Set (Fin n → ℝ),
      G.CliqueFree 5 ∧ (edgeFamily G).card = 3*n-5 ∧
      HasTreewidthAtMost G 4 ∧ ¬HasTreewidthAtMost G 3 ∧
      LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      actualDirectionGraph Q = G ∧
      IsMinkowskiSummand Q (((n-6 : ℕ) : ℝ) • graphicalZonotope G) ∧
      (∀ H : SimpleGraph (Fin n),H < G →
        ¬∃ R : Set (Fin n → ℝ),IsFinitePolytope R ∧
          PolytopalMinkowskiIndecomposable R ∧ FullDimension R ∧
          IsWeakMinkowskiSummand R (graphicalZonotope H)) ∧
      ¬∃ H : SimpleGraph (Fin n),H ≤ G ∧ IsThreeTree H ∧
        ∃ R : Set (Fin n → ℝ),IsFinitePolytope R ∧
          PolytopalMinkowskiIndecomposable R ∧ FullDimension R ∧
          IsWeakMinkowskiSummand R (graphicalZonotope H) := by sorry

/-- Complete corresponding principal theorem, including its quantitative witness. -/
theorem TwoHub.two_singleton_classification : Targets.TwoSingletonClassification := by sorry

/-- Complete corresponding principal theorem, including its quantitative witness. -/
theorem four_partite_spanning_threeTrees : Targets.FourPartiteSpanningThreeTrees := by sorry

/-- Complete corresponding principal theorem, including its quantitative witness. -/
theorem threeTree_lattice_dilation : Targets.ThreeTreeLatticeDilation := by sorry

/-- Complete corresponding principal theorem, including its quantitative witness. -/
theorem unit_lattice_classification : Targets.UnitLatticeClassification := by sorry

/-- Complete corresponding principal theorem, including its quantitative witness. -/
theorem optimal_k5_free_dilation : Targets.OptimalK5FreeDilation := by sorry

namespace DoubledParts
/-- Both exact lattice summands and all parity-specific Boolean phase conclusions. -/
def PrincipalBooleanPhaseClaim : Prop :=
  ∀ r : ℕ,4≤ r → ∃ Q R : Set ((Fin r×Fin 2) → ℝ),
    LatticePolytope Q ∧ LatticePolytope R ∧
    MinkowskiIndecomposable Q ∧ MinkowskiIndecomposable R ∧
    FullDimension Q ∧ FullDimension R ∧
    Q+R=graphicalZonotope (doubledPartGraph r) ∧
    actualDirectionGraph Q=doubledPartGraph r ∧ actualDirectionGraph R=doubledPartGraph r ∧
    BooleanElemental Q ∧ BooleanElemental R ∧
    (Even r → CentrallySymmetricUpToTranslation Q ∧ CentrallySymmetricUpToTranslation R) ∧
    (Odd r → ∃ t,R=({t} : Set ((Fin r×Fin 2) → ℝ))+(-1 : ℝ) • Q) ∧
    (Odd r → graphicalZonotope (doubledPartGraph r)=
      Q+(-1 : ℝ) • Q+({fun _ : Fin r×Fin 2 => ((r-1 : ℕ) : ℝ)} : Set ((Fin r×Fin 2) → ℝ)))
/-- The full Theorem 9.8, with both complementary lattice indecomposables. -/
theorem principal_boolean_phase_theorem : PrincipalBooleanPhaseClaim := by sorry
end DoubledParts

end PalomarGraphicalMain
namespace PalomarGraphicalMain.PathResults
open PalomarGraphicalMain
/-- Theorems 3.1 and 4.1 attainment for the original third-power path family. -/
theorem principal_path_theorem {n : ℕ} (hn : 4 ≤ n) :
    ∃ Q R : Set (Fin n → ℝ),
      IsGeneralizedPermutahedron Q ∧ PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
      LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = n-1 ∧
      Q + R = (2 : ℝ) • graphicalZonotope (Path.graph n) ∧
      (∀ u v, ActualRootEdge Q u v ↔ (Path.graph n).Adj u v) ∧
      (∀ p q, IsExposedSegment Q p q →
        ∃ u v, (Path.graph n).Adj u v ∧ ∃ t : ℝ, t ≠ 0 ∧
          q-p = t • (basisVector v-basisVector u)) ∧
      HasPlaneStraightLineDrawing (Path.graph n) ∧
      (Path.graph n).CliqueFree 5 ∧ (edgeFamily (Path.graph n)).card = 3*n-6 ∧
      (Path.graph n).maxDegree = min (n-1) 6 := by sorry
end PalomarGraphicalMain.PathResults
