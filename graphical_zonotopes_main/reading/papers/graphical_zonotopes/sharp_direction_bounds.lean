module

public import Papers.GraphicalZonotopes.DirectionBounds
public import Papers.GraphicalZonotopes.RootDirectionLines
public import Papers.GraphicalZonotopes.PathPrincipal

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open scoped Pointwise

/-- The root-direction graph counts every geometric edge direction of an
actual generalized permutahedron. This includes arbitrary translations. -/
theorem generalizedPermutahedron_exposed_edge_is_root
    {V : Type*} [Fintype V] [DecidableEq V] {Q : Set (V → ℝ)}
    (hQ : IsGeneralizedPermutahedron Q) {p q : V → ℝ}
    (hex : IsExposedSegment Q p q) :
    ∃ u v : V,u≠v ∧ ∃ t : ℝ,t≠0 ∧
      q-p=t • (basisVector v-basisVector u) := by
  obtain ⟨z,hn,hs,rfl⟩ := hQ
  have hweak : IsWeakMinkowskiSummand (basePolytope z)
      (graphicalZonotope (⊤ : SimpleGraph V)) := by
    apply (isWeakMinkowskiSummand_graphical_iff hn hs).mpr
    intro u v huv hnon
    exact False.elim (hnon huv)
  obtain ⟨a,ha,R,_,_,_,he⟩ := hweak
  obtain ⟨u,v,huv,t,ht,heq⟩ :=
    basePolytope_summand_exposed_edge hn hs (⊤ : SimpleGraph V) ha.le R he hex
  exact ⟨u,v,huv,t,ht,heq⟩

namespace Path

theorem actualDirectionGraph_eq {n : ℕ} (hn : 4≤n) :
    actualDirectionGraph (polytope n)=graph n := by
  apply SimpleGraph.ext
  funext u v
  exact propext (actual_direction_graph hn u v)

theorem polytope_generalizedPermutahedron (n : ℕ) :
    IsGeneralizedPermutahedron (polytope n) :=
  ⟨setFunction n,(setFunction_normalized n).1,setFunction_supermodular n,rfl⟩

theorem polytope_polytopalIndecomposable {n : ℕ} (hn : 4≤n) :
    PolytopalMinkowskiIndecomposable (polytope n) :=
  (minkowskiIndecomposable_iff_polytopal (polytope_generalizedPermutahedron n)).mp
    (polytope_indecomposable hn)

theorem polytope_fullDimension {n : ℕ} (hn : 4≤n) :
    FullDimension (polytope n) := by
  simpa only [FullDimension,Fintype.card_fin] using polytope_dimension hn

theorem directionCount_eq {n : ℕ} (hn : 4≤n) :
    directionCount (polytope n)=3*n-6 := by
  rw [directionCount,actualDirectionGraph_eq hn]
  exact graph_edge_count hn

theorem maximumDirectionDegree_eq {n : ℕ} (hn : 4≤n) :
    maximumDirectionDegree (polytope n)=min (n-1) 6 := by
  classical
  letI : DecidableRel (graph n).Adj := graph_decidableAdj n
  change (actualDirectionGraph (polytope n)).maxDegree=min (n-1) 6
  let e : actualDirectionGraph (polytope n) ≃g graph n :=
    { toEquiv := Equiv.refl _
      map_rel_iff' := by
        intro u v
        exact (actual_direction_graph hn u v).symm }
  exact e.maxDegree_eq.trans (graph_maxDegree hn)

end Path

/-- The full content of Theorem4.1: both universal sharp bounds, the equality
classification, and simultaneous attainment by the paper's explicit Q_n for
every n≥4. The definition uses ordinary polytopal indecomposability. -/
def SharpDirectionBounds : Prop :=
  (∀ n : ℕ,4≤n → ∀ Q : Set (Fin n → ℝ),
    IsGeneralizedPermutahedron Q → PolytopalMinkowskiIndecomposable Q →
    FullDimension Q →
    3*n-6≤directionCount Q ∧ min (n-1) 6≤maximumDirectionDegree Q ∧
    (directionCount Q=3*n-6 → IsThreeTree (actualDirectionGraph Q))) ∧
  ∀ n : ℕ,4≤n →
    IsGeneralizedPermutahedron (Path.polytope n) ∧
    PolytopalMinkowskiIndecomposable (Path.polytope n) ∧
    FullDimension (Path.polytope n) ∧
    directionCount (Path.polytope n)=3*n-6 ∧
    maximumDirectionDegree (Path.polytope n)=min (n-1) 6

/-- A single audited endpoint is required for the entire sharp theorem,
including the explicit equality witnesses in its final sentence. -/
theorem sharp_direction_bounds : SharpDirectionBounds := by
  refine ⟨direction_bounds_polytopal,?_⟩
  intro n hn
  exact ⟨Path.polytope_generalizedPermutahedron n,
    Path.polytope_polytopalIndecomposable hn,Path.polytope_fullDimension hn,
    Path.directionCount_eq hn,Path.maximumDirectionDegree_eq hn⟩

end GraphicalZonotopes
