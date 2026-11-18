module

public import Papers.GraphicalZonotopes.GraphDefinitions
public import Papers.GraphicalZonotopes.TreewidthDefinition
public import Papers.GraphicalZonotopes.PathSupport
public import Papers.GraphicalZonotopes.SmallPartTarget

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace Targets
open Finset
open scoped BigOperators Pointwise
attribute [local instance] Classical.propDecidable

/-!
These are explicit proposition-valued targets for the principal results beyond
Theorem 3.1. They are NOT axioms and their presence does not assert their truth.
No theorem is exported merely by defining its intended statement. The final
audit must match each of these targets to a separately kernel-checked proof.
-/

/-- Theorem 4.1. In particular there is no clique-number restriction. -/
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
end GraphicalZonotopes
