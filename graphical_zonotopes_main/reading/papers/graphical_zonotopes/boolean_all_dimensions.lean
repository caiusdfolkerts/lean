module

public import Papers.GraphicalZonotopes.FourSmallParts

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped Pointwise

theorem booleanPair_on_fin {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (D : BooleanPairData G) (hG : G.Connected)
    {n : ℕ} (hc : Fintype.card V=n) :
    ∃ H : SimpleGraph (Fin n),H.Connected ∧ Nonempty (BooleanPairData H) := by
  let e : Fin n ≃ V := Fintype.equivOfCardEq (by simpa using hc.symm)
  let E : G.comap e ≃g G := {toEquiv := e,map_rel_iff' := by intros; rfl}
  exact ⟨G.comap e,E.connected_iff.mpr hG,⟨D.relabel e⟩⟩

theorem SmallBoolean.partGraph_connected {n : ℕ} (part : Fin n → Fin 4)
    (z o : Fin n) (hzo : part z≠part o) : (SmallBoolean.partGraph part).Connected := by
  letI : Nonempty (Fin n) := ⟨z⟩
  refine ⟨?_⟩
  intro u v
  by_cases huv : part u≠part v
  · exact SimpleGraph.Adj.reachable huv
  · have he : part u=part v := not_not.mp huv
    by_cases huz : part u=part z
    · exact (SimpleGraph.Adj.reachable (show (SmallBoolean.partGraph part).Adj u o from
        by change part u≠part o; simpa [huz] using hzo)).trans
        (SimpleGraph.Adj.reachable (show (SmallBoolean.partGraph part).Adj o v from
          by change part o≠part v; simpa [← he,huz] using Ne.symm hzo))
    · exact (SimpleGraph.Adj.reachable (show (SmallBoolean.partGraph part).Adj u z from huz)).trans
        (SimpleGraph.Adj.reachable (show (SmallBoolean.partGraph part).Adj z v from
          by change part z≠part v; simpa [← he] using Ne.symm huz))

theorem booleanPair_every_vertex_count {n : ℕ} (hn : 4≤n) :
    ∃ G : SimpleGraph (Fin n),G.Connected ∧ Nonempty (BooleanPairData G) := by
  by_cases hn4 : n=4
  · subst n
    exact ⟨SmallBoolean.K4.graph,
      SmallBoolean.partGraph_connected SmallBoolean.K4.part 0 1 (by decide),
      ⟨SmallBoolean.K4.pairData⟩⟩
  by_cases hn5 : n=5
  · subst n
    exact ⟨SmallBoolean.K1112.graph,
      SmallBoolean.partGraph_connected SmallBoolean.K1112.part 0 1 (by decide),
      ⟨SmallBoolean.K1112.pairData⟩⟩
  by_cases hn6 : n=6
  · subst n
    exact ⟨SmallBoolean.K1122.graph,
      SmallBoolean.partGraph_connected SmallBoolean.K1122.part 0 1 (by decide),
      ⟨SmallBoolean.K1122.pairData⟩⟩
  have hn7 : 7≤n := by omega
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨r,hr⟩ := he
    have hr4 : 4≤r := by omega
    exact booleanPair_on_fin (DoubledParts.doubledPairData (I := Fin r) (by simpa using hr4))
      (DoubledParts.graph_connected (by simpa using (show 2≤r by omega))) (by
        simp only [Fintype.card_prod,Fintype.card_fin]
        omega)
  · obtain ⟨r,hr⟩ := ho
    have hr4 : 4≤r+1 := by omega
    let a : Fin (r+1) := 0
    apply booleanPair_on_fin
      (DoubledParts.singletonPairData (I := Fin (r+1)) (by simpa using hr4) a)
      (DoubledParts.singletonGraph_connected (by simpa using (show 2≤r+1 by omega)) a)
    change Fintype.card {v : Fin (r+1)×Fin 2 // v≠(a,1)}=n
    rw [card_ne_subtype]
    simp only [Fintype.card_prod,Fintype.card_fin]
    omega

/-- The unbounded final consequence of Corollary9.11: both summands are
actual lattice polytopes in every dimension at least three. -/
theorem boolean_decomposition_every_dimension {d : ℕ} (hd : 3≤d) :
    ∃ G : SimpleGraph (Fin (d+1)),∃ Q R : Set (Fin (d+1) → ℝ),
      LatticePolytope Q ∧ LatticePolytope R ∧
      MinkowskiIndecomposable Q ∧ MinkowskiIndecomposable R ∧
      Module.finrank ℝ (vectorSpan ℝ Q)=d ∧ Module.finrank ℝ (vectorSpan ℝ R)=d ∧
      Q+R=graphicalZonotope G ∧ BooleanElemental Q ∧ BooleanElemental R := by
  obtain ⟨G,hG,⟨D⟩⟩ := booleanPair_every_vertex_count (show 4≤d+1 by omega)
  obtain ⟨hL,hR,hI,hJ,hD,hE,hS,hgraph,hgraph',hB,hB'⟩ := D.geometric_pair hG
  refine ⟨G,basePolytope D.left,basePolytope D.right,hL,hR,hI,hJ,?_,?_,hS,hB,hB'⟩
  · simpa only [FullDimension,Fintype.card_fin,Nat.add_sub_cancel] using hD
  · simpa only [FullDimension,Fintype.card_fin,Nat.add_sub_cancel] using hE

end GraphicalZonotopes
