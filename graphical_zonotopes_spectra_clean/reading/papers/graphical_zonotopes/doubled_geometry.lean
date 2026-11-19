module

public import Papers.GraphicalZonotopes.GraphDefinitions

public import Papers.GraphicalZonotopes.DoubledConnectivity
public import Papers.GraphicalZonotopes.ConnectedDimension
public import Papers.GraphicalZonotopes.SummandEdges

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace DoubledParts
open Finset
open scoped Pointwise
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem setFunction_ne_zero (hI : 3≤Fintype.card I) : (setFunction (I := I))≠0 := by
  obtain ⟨e⟩ := slopeEdge_nonempty (by omega : 2≤Fintype.card I)
  obtain ⟨S,hu,hv,hd⟩ := setFunction_nonzero_slack hI e.2
  intro he
  rw [he] at hd
  exact hd (by simp [delta])

theorem complementFunction_ne_zero (hI : 3≤Fintype.card I) : (complementFunction (I := I))≠0 := by
  obtain ⟨e⟩ := slopeEdge_nonempty (by omega : 2≤Fintype.card I)
  obtain ⟨S,hu,hv,hd⟩ := complementFunction_nonzero_slack hI e.2
  intro he
  rw [he] at hd
  exact hd (by simp [delta])

theorem setFunction_extreme (hI : 4≤Fintype.card I) :
    ExtremeSupermodular (setFunction (I := I)) := by
  apply extremeSupermodular_of_local_row_lines setFunction_translationNormalized
    setFunction_supermodular (setFunction_ne_zero (by omega)) setFunction_graphical
  · exact coefficientEdgeGraph_connected hI (fun C hc hC => mobius_setFunction_four_ne_zero hc hC)
  · exact setFunction_local_row_lines (by omega)

theorem complementFunction_extreme (hI : 4≤Fintype.card I) :
    ExtremeSupermodular (complementFunction (I := I)) := by
  apply extremeSupermodular_of_local_row_lines complementFunction_translationNormalized
    complementFunction_supermodular (complementFunction_ne_zero (by omega)) complementFunction_graphical
  · exact coefficientEdgeGraph_connected hI (fun C hc hC => mobius_complementFunction_four_ne_zero hc hC)
  · exact complementFunction_local_row_lines (by omega)

theorem polytope_indecomposable (hI : 4≤Fintype.card I) :
    MinkowskiIndecomposable (polytope (I := I)) :=
  (setFunction_extreme hI).minkowskiIndecomposable

theorem complementPolytope_indecomposable (hI : 4≤Fintype.card I) :
    MinkowskiIndecomposable (complementPolytope (I := I)) :=
  (complementFunction_extreme hI).minkowskiIndecomposable

theorem polytope_fullDimension (hI : 3≤Fintype.card I) :
    FullDimension (polytope (I := I)) := by
  apply finrank_vectorSpan_eq_of_connected_slacks setFunction_translationNormalized.1
    setFunction_supermodular (graph_connected (by omega))
  intro u v huv
  exact setFunction_nonzero_slack hI huv

theorem complementPolytope_fullDimension (hI : 3≤Fintype.card I) :
    FullDimension (complementPolytope (I := I)) := by
  apply finrank_vectorSpan_eq_of_connected_slacks complementFunction_translationNormalized.1
    complementFunction_supermodular (graph_connected (by omega))
  intro u v huv
  exact complementFunction_nonzero_slack hI huv

theorem polytope_actualDirectionGraph (hI : 3≤Fintype.card I) :
    actualDirectionGraph (polytope (I := I))=graph I := by
  ext u v
  constructor
  · apply basePolytope_summand_actualRootEdge setFunction_translationNormalized.1
      setFunction_supermodular (graph I) (by norm_num : (0 : ℝ)≤1) complementPolytope
    simpa only [one_smul,polytope] using (polytope_add_complement (I := I))
  · intro huv
    obtain ⟨S,hu,hv,hd⟩ := setFunction_nonzero_slack hI huv
    apply exposedSegment_of_positive_delta setFunction_translationNormalized.1
      setFunction_supermodular ((graph I).ne_of_adj huv) hu hv
    have hnon := setFunction_supermodular.elemental u v ((graph I).ne_of_adj huv) S hu hv
    exact lt_of_le_of_ne hnon (Ne.symm hd)

theorem complementPolytope_actualDirectionGraph (hI : 3≤Fintype.card I) :
    actualDirectionGraph (complementPolytope (I := I))=graph I := by
  ext u v
  constructor
  · apply basePolytope_summand_actualRootEdge complementFunction_translationNormalized.1
      complementFunction_supermodular (graph I) (by norm_num : (0 : ℝ)≤1) polytope
    simpa only [one_smul,add_comm,complementPolytope] using (polytope_add_complement (I := I))
  · intro huv
    obtain ⟨S,hu,hv,hd⟩ := complementFunction_nonzero_slack hI huv
    apply exposedSegment_of_positive_delta complementFunction_translationNormalized.1
      complementFunction_supermodular ((graph I).ne_of_adj huv) hu hv
    have hnon := complementFunction_supermodular.elemental u v ((graph I).ne_of_adj huv) S hu hv
    exact lt_of_le_of_ne hnon (Ne.symm hd)

/-- Every geometric edge is covered by the root-direction graph. -/
theorem every_polytope_edge_is_root {p q : (I×Fin 2) → ℝ}
    (h : IsExposedSegment polytope p q) :
    ∃ u v,(graph I).Adj u v ∧ ∃ t : ℝ,t≠0 ∧
      q-p=t • (basisVector v-basisVector u) := by
  apply basePolytope_summand_exposed_edge setFunction_translationNormalized.1
    setFunction_supermodular (graph I) (by norm_num : (0 : ℝ)≤1) complementPolytope _ h
  simpa only [one_smul,polytope] using (polytope_add_complement (I := I))

theorem every_complementPolytope_edge_is_root {p q : (I×Fin 2) → ℝ}
    (h : IsExposedSegment complementPolytope p q) :
    ∃ u v,(graph I).Adj u v ∧ ∃ t : ℝ,t≠0 ∧
      q-p=t • (basisVector v-basisVector u) := by
  apply basePolytope_summand_exposed_edge complementFunction_translationNormalized.1
    complementFunction_supermodular (graph I) (by norm_num : (0 : ℝ)≤1) polytope _ h
  simpa only [one_smul,add_comm,complementPolytope] using (polytope_add_complement (I := I))

theorem polytope_booleanElemental : BooleanElemental (polytope (I := I)) := by
  intro u v huv S hu hv
  rw [polytope,lowerSupport_basePolytope setFunction_translationNormalized.1 setFunction_supermodular]
  exact setFunction_boolean huv hu hv

theorem complementPolytope_booleanElemental : BooleanElemental (complementPolytope (I := I)) := by
  intro u v huv S hu hv
  rw [complementPolytope,lowerSupport_basePolytope complementFunction_translationNormalized.1
    complementFunction_supermodular]
  by_cases he : (graph I).Adj u v
  · rw [complementFunction,delta_sub,graphFunction_delta _ huv hu hv,if_pos he]
    rcases setFunction_boolean huv hu hv with h | h
    · exact Or.inr (by rw [h]; norm_num)
    · exact Or.inl (by rw [h]; norm_num)
  · exact Or.inl (complementFunction_graphical u v huv he S hu hv)

end DoubledParts
end GraphicalZonotopes
