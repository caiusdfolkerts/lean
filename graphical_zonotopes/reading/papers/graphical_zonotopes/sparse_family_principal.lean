module

public import Papers.GraphicalZonotopes.SparseFamilyTreewidth
public import Papers.GraphicalZonotopes.SparseFamilyMinimality
public import Papers.GraphicalZonotopes.PolytopalWeakSummands
public import Papers.GraphicalZonotopes.PrincipalTargets

/-! # Theorem 8.2 in its complete geometric form

Every order `n ≥ 10` has a genuine graph of treewidth exactly four and a
full-dimensional lattice indecomposable summand in the asserted dilation.
The actual exposed-root direction graph is proved equal to that graph, and
every proper edge-subgraph is excluded from supporting a full-dimensional ray.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.SparseFamily
open Finset SetFunctionEmbedding
open scoped BigOperators Pointwise

theorem complete_family (n : ℕ) (hn : 10 ≤ n) :
    ∃ G : SimpleGraph (Fin n), ∃ Q : Set (Fin n → ℝ),
      G.CliqueFree 5 ∧ (edgeFamily G).card = 3*n-5 ∧
      HasTreewidthAtMost G 4 ∧ ¬HasTreewidthAtMost G 3 ∧
      EdgeMinimalSupporting G ∧ LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      FullDimension Q ∧ actualDirectionGraph Q = G ∧
      IsMinkowskiSummand Q (((n-6 : ℕ) : ℝ) • graphicalZonotope G) ∧
      ¬∃ H : SimpleGraph (Fin n), H ≤ G ∧ IsThreeTree H ∧ SupportsFullIndecomposable H := by
  let m := n-10
  have hcard : Fintype.card (Vertex m) = n := by rw [vertex_card]; dsimp [m]; omega
  letI : Nonempty (Vertex m) := (connected m).nonempty
  let e : Vertex m ≃ Fin n := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hcard)
  let G : SimpleGraph (Fin n) := (graph m).map e.toEmbedding
  let z : SetFunction (Fin n) := extend e.toEmbedding (function m)
  have hz : ExtremeSupermodular z := extend_extreme e.toEmbedding (extreme m)
  have hzi : IntegerValued z := extend_integer e.toEmbedding (integerValued m)
  have hzg : Graphical G z := by
    apply extend_graphical e.toEmbedding
    change Graphical (((graph m).map e.toEmbedding).comap e.toEmbedding) (function m)
    rw [SimpleGraph.comap_map_eq]
    exact graphical m
  have hM : m+4 = n-6 := by dsimp [m]; omega
  have hbound : ∀ u v : Fin n, u ≠ v → ∀ S, u ∉ S → v ∉ S → delta z u v S ≤ (n-6 : ℕ) := by
    intro u v huv S hu hv
    obtain ⟨a,rfl⟩ := e.surjective u
    obtain ⟨b,rfl⟩ := e.surjective v
    change delta (extend e.toEmbedding (function m)) (e.toEmbedding a) (e.toEmbedding b) S ≤ _
    rw [delta_extend e.toEmbedding (function m) a b S]
    simpa only [hM] using elemental_upper m a b (fun he => huv (congrArg e he))
      (pullSet e.toEmbedding S) (by simpa only [mem_pullSet,Equiv.toEmbedding_apply] using hu)
      (by simpa only [mem_pullSet,Equiv.toEmbedding_apply] using hv)
  have hsum : IsMinkowskiSummand (basePolytope z)
      (((n-6 : ℕ) : ℝ) • graphicalZonotope G) := by
    apply (isMinkowskiSummand_graphical_iff hz.1.1 hz.2.1 (Nat.cast_nonneg (n-6))).mpr
    exact ⟨hzg,fun u v huv _ S hu hv => hbound u v huv S hu hv⟩
  have hdim : FullDimension (basePolytope z) := by
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope (extend e.toEmbedding (function m)))) = _
    rw [finrank_vectorSpan_extend e.toEmbedding (extreme m).1]
    have hd := full_dimension m
    change Module.finrank ℝ (vectorSpan ℝ (basePolytope (function m))) =
      Fintype.card (Vertex m)-1 at hd
    simpa only [hcard,Fintype.card_fin] using hd
  have hactual : actualDirectionGraph (basePolytope z) = G := by
    apply SimpleGraph.ext
    funext u v
    apply propext
    constructor
    · intro he
      obtain ⟨R,hR,hRc,hnR,hQR⟩ := hsum
      exact basePolytope_summand_actualRootEdge hz.1.1 hz.2.1 G
        (Nat.cast_nonneg (n-6)) R hQR he
    · intro he
      obtain ⟨a,b,hab,rfl,rfl⟩ := (SimpleGraph.map_adj e.toEmbedding (graph m) u v).mp he
      obtain ⟨S,ha,hb,hp⟩ := positive_slack m a b hab
      apply exposedSegment_of_positive_delta hz.1.1 hz.2.1
        (fun he => hab.ne (e.injective he)) (S := S.map e.toEmbedding)
        (by simpa using ha) (by simpa using hb)
      change 0 < delta (extend e.toEmbedding (function m))
        (e.toEmbedding a) (e.toEmbedding b) (S.map e.toEmbedding)
      rw [delta_extend e.toEmbedding (function m) a b (S.map e.toEmbedding),pullSet_map]
      exact hp
  have hcf : G.CliqueFree 5 := SimpleGraph.cliqueFree_map_iff.mpr (cliqueFree_five m)
  have hedge : (edgeFamily G).card = 3*n-5 := by
    change (edgeFamily ((graph m).map e.toEmbedding)).card = _
    rw [edgeFamily_card_map,edge_count]
    dsimp [m]
    omega
  have hw4 : HasTreewidthAtMost G 4 := by
    have hh := (width_at_most_four m).comap e.symm.toEmbedding
    rwa [SimpleGraph.comap_symm] at hh
  have hnw3 : ¬HasTreewidthAtMost G 3 := by
    intro hh
    have hback := hh.comap e.toEmbedding
    rw [show G = (graph m).map e.toEmbedding from rfl,SimpleGraph.comap_map_eq] at hback
    exact not_width_three m hback
  have hno : ¬HasAdmissibleSpanningThreeTree G := by
    intro hh
    have hback := hh.map_equiv e.symm
    rw [SimpleGraph.map_symm,show G = (graph m).map e.toEmbedding from rfl,
      SimpleGraph.comap_map_eq] at hback
    exact no_admissible_spanning m hback
  have hsupport : SupportsFullIndecomposable G :=
    ⟨basePolytope z,(show IsGeneralizedPermutahedron (basePolytope z) from
      ⟨z,hz.1.1,hz.2.1,rfl⟩).finitePolytope,hz.minkowskiIndecomposable,hdim,
      (n-6 : ℕ),by exact_mod_cast (show 0 < n-6 by omega),hsum⟩
  refine ⟨G,basePolytope z,hcf,hedge,hw4,hnw3,
    edgeMinimalSupporting_of_one_excess (by omega) hedge hno hsupport,
    hzi.basePolytope hz.1.1 hz.2.1,hz.minkowskiIndecomposable,hdim,hactual,hsum,?_⟩
  rintro ⟨H,hHG,hH,hS⟩
  exact hno ⟨H,hHG,hH,(threeTree_supports_iff_admissible (by omega) hH).mp hS⟩

/-- The exact pinned principal target, discharged by the stronger literal
statement above, including all orders and the asserted dilation. -/
theorem paper_theorem_8_2 : Targets.SparseTreewidthFourFamily := by
  intro n hn
  obtain ⟨G,Q,hcf,he,hw4,hnw3,hmin,hQ,hI,hD,hA,hS,hno⟩ := complete_family n hn
  exact ⟨G,hcf,he,hw4,hnw3,hmin,Q,hQ,hI,hD,hS⟩

/-- The same family using only ordinary polytopal indecomposability. The
proper-subgraph conclusion is expanded explicitly so the convention used
inside `EdgeMinimalSupporting` is not an implicit semantic assumption. -/
theorem paper_theorem_8_2_polytopal (n : ℕ) (hn : 10 ≤ n) :
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
          IsWeakMinkowskiSummand R (graphicalZonotope H) := by
  obtain ⟨G,Q,hcf,he,hw4,hnw3,hmin,hQ,hI,hD,hA,hS,hno⟩ := complete_family n hn
  have hpoly : PolytopalMinkowskiIndecomposable Q :=
    ⟨hI.1,fun P R hP hR hsum => hI.2 P R hP.compact hR.compact hP.convex hR.convex hsum⟩
  refine ⟨G,Q,hcf,he,hw4,hnw3,hQ,hpoly,hD,hA,hS,?_,?_⟩
  · intro H hHG
    rintro ⟨R,hR,hi,hd,hs⟩
    exact hmin.2 H hHG
      ⟨R,hR,(weakSummand_indecomposable_iff_polytopal hR hs).mpr hi,hd,hs⟩
  · rintro ⟨H,hHG,hH,R,hR,hi,hd,hs⟩
    exact hno ⟨H,hHG,hH,
      R,hR,(weakSummand_indecomposable_iff_polytopal hR hs).mpr hi,hd,hs⟩

end GraphicalZonotopes.SparseFamily
