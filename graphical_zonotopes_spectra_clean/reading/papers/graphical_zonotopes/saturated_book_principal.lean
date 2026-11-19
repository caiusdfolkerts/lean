module

public import Papers.GraphicalZonotopes.SaturatedBookGeometry
public import Papers.GraphicalZonotopes.SaturatedGeneralAttainment
public import Papers.GraphicalZonotopes.SaturatedFourAttainment
public import Papers.GraphicalZonotopes.SmallCountPrincipal
public import Papers.GraphicalZonotopes.PolytopalWeakSummands
public import Papers.GraphicalZonotopes.SaturatedBookArithmetic

/-! # The minimum number of directions in a saturated clique book

This is the literal quantified lower bound and lattice equality witness of
Theorem 7.12.  Both use actual edges of actual convex polytopes.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.SaturatedDirections
open Finset
open scoped BigOperators Pointwise
attribute [local instance] Classical.propDecidable

theorem small_spoke_attainment (s : ℕ) (hs : s = 2 ∨ s = 3) :
    ∃ f : SetFunction (Fin s ⊕ Fin (cliqueCapacity s)),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s (cliqueCapacity s)) f ∧ FullDimension (basePolytope f) ∧
      LatticePolytope (basePolytope f) ∧
      ∀ a : Fin s,(univ.filter (fun j : Fin (cliqueCapacity s) =>
        ActualRootEdge (basePolytope f) (Sum.inl a) (Sum.inr j))).card =
          saturatedHubNeighbors s := by
  have hs2 : 2 ≤ s := by omega
  have hk : 1 ≤ cliqueCapacity s := by
    rcases hs with rfl | rfl <;> norm_num [cliqueCapacity,Nat.choose]
  have hchoose : cliqueCapacity s ≤ s.choose 2 := by
    rcases hs with rfl | rfl <;> norm_num [cliqueCapacity,Nat.choose]
  have hUs : saturatedHubNeighbors s = cliqueCapacity s := by
    rcases hs with rfl | rfl <;> norm_num [saturatedHubNeighbors,cliqueCapacity,Nat.choose]
  obtain ⟨f,hn,hi,he,hG,hd,hm,hl,R,hR,hRn,hQR⟩ :=
    BooleanModule.small_count_lattice_books s (cliqueCapacity s) hs2 hk hchoose
  have hfinite : IsFinitePolytope (basePolytope f) :=
    IsGeneralizedPermutahedron.finitePolytope ⟨f,hn.1,he.2.1,rfl⟩
  have hweak := (isWeakMinkowskiSummand_graphical_iff hn.1 he.2.1).mpr hG
  obtain ⟨hsub,hh,hsp⟩ := actual_hub_spoke_lower hs2 hfinite hm hd hweak
  refine ⟨f,hn,hi,he,hG,hd,hl,?_⟩
  intro a
  apply le_antisymm
  · rw [hUs]
    exact (card_filter_le _ _).trans (by simp)
  · exact hsp a

theorem all_spoke_attainment (s : ℕ) (hs : 2 ≤ s) :
    ∃ f : SetFunction (Fin s ⊕ Fin (cliqueCapacity s)),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s (cliqueCapacity s)) f ∧ FullDimension (basePolytope f) ∧
      LatticePolytope (basePolytope f) ∧
      ∀ a : Fin s,(univ.filter (fun j : Fin (cliqueCapacity s) =>
        ActualRootEdge (basePolytope f) (Sum.inl a) (Sum.inr j))).card =
          saturatedHubNeighbors s := by
  by_cases hs5 : 5 ≤ s
  · exact BooleanModule.Saturated.spoke_attainment s hs5
  by_cases hs4 : s = 4
  · subst s
    have hc : cliqueCapacity 4 = 14 := by norm_num [cliqueCapacity,Nat.choose]
    have hu : saturatedHubNeighbors 4 = 12 := by
      norm_num [saturatedHubNeighbors,cliqueCapacity,Nat.choose]
    rw [hc,hu]
    exact BooleanModule.SaturatedFour.spoke_attainment
  · exact small_spoke_attainment s (by omega)

/-- The exact minimum is attained by a lattice polytope in every allowed
hub size, with equality at every individual hub. -/
theorem lattice_equality (s : ℕ) (hs : 2 ≤ s) :
    ∃ Q : Set ((Fin s ⊕ Fin (cliqueCapacity s)) → ℝ),
      LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧ FullDimension Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s (cliqueCapacity s))) ∧
      directionCount Q = s.choose 2 + s*saturatedHubNeighbors s ∧
      ∀ a : Fin s,(univ.filter (fun j : Fin (cliqueCapacity s) =>
        ActualRootEdge Q (Sum.inl a) (Sum.inr j))).card = saturatedHubNeighbors s := by
  obtain ⟨f,hn,hi,he,hG,hd,hl,hsp⟩ := all_spoke_attainment s hs
  have hfinite : IsFinitePolytope (basePolytope f) :=
    IsGeneralizedPermutahedron.finitePolytope ⟨f,hn.1,he.2.1,rfl⟩
  have hm := he.minkowskiIndecomposable
  have hw := (isWeakMinkowskiSummand_graphical_iff hn.1 he.2.1).mpr hG
  obtain ⟨hsub,hh,_⟩ := actual_hub_spoke_lower hs hfinite hm hd hw
  exact ⟨basePolytope f,hl,hm,hd,hw,
    BookEdges.edge_count_eq (actualDirectionGraph (basePolytope f)) hsub hh
      (saturatedHubNeighbors s) hsp,hsp⟩

/-- Theorem 7.12 of the paper, with the universal lower bound and the
unconditional lattice equality witness in one statement. -/
theorem paper_theorem_7_12 :
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
          ActualRootEdge Q (Sum.inl i) (Sum.inr j))).card = saturatedHubNeighbors s := by
  intro s hs
  refine ⟨?_,lattice_equality s hs⟩
  intro Q hQ hi hd hw
  obtain ⟨hsub,hh,hsp⟩ := actual_hub_spoke_lower hs hQ hi hd hw
  exact ⟨direction_lower hs hQ hi hd hw,fun _ => hh,hsp⟩

/-- The same principal theorem with the paper's ordinary definition of
indecomposability, quantifying over polytopal Minkowski decompositions. -/
theorem paper_theorem_7_12_polytopal :
    ∀ s : ℕ,2 ≤ s →
      (∀ Q : Set ((Fin s ⊕ Fin (cliqueCapacity s)) → ℝ),
        IsFinitePolytope Q → PolytopalMinkowskiIndecomposable Q → FullDimension Q →
        IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s (cliqueCapacity s))) →
        s.choose 2 + s*saturatedHubNeighbors s ≤ directionCount Q ∧
        (3 ≤ s → ∀ i j : Fin s,i ≠ j → ActualRootEdge Q (Sum.inl i) (Sum.inl j)) ∧
        ∀ i : Fin s,saturatedHubNeighbors s ≤
          (univ.filter (fun j : Fin (cliqueCapacity s) =>
            ActualRootEdge Q (Sum.inl i) (Sum.inr j))).card) ∧
      ∃ Q : Set ((Fin s ⊕ Fin (cliqueCapacity s)) → ℝ),
        LatticePolytope Q ∧ PolytopalMinkowskiIndecomposable Q ∧ FullDimension Q ∧
        IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s (cliqueCapacity s))) ∧
        directionCount Q = s.choose 2 + s*saturatedHubNeighbors s ∧
        ∀ i : Fin s,(univ.filter (fun j : Fin (cliqueCapacity s) =>
          ActualRootEdge Q (Sum.inl i) (Sum.inr j))).card = saturatedHubNeighbors s := by
  intro s hs
  obtain ⟨hlower,Q,hL,hI,hD,hW,hE,hS⟩ := paper_theorem_7_12 s hs
  refine ⟨?_,Q,hL,?_,hD,hW,hE,hS⟩
  · intro Q hQ hi hd hw
    exact hlower Q hQ ((weakSummand_indecomposable_iff_polytopal hQ hw).mpr hi) hd hw
  · exact ⟨hI.1,fun P R hP hR he =>
      hI.2 P R hP.compact hR.compact hP.convex hR.convex he⟩

end GraphicalZonotopes.SaturatedDirections
