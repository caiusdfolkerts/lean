module

public import Papers.GraphicalZonotopes.DiamondGeometry
public import Papers.GraphicalZonotopes.TriangularExtensionGeometry

/-! # An unbounded family with one edge above the sharp direction bound

The graphs are precisely the graphs `L_(10+m)` in Section 8.2. The polynomial
is an alternative uniform construction: at each step append the Boolean
marginal `b ∧ (a ∨ t)`, then exchange the names of the two hubs. This retains
all old directions and raises the maximum elemental slack by at most one.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace SparseFamily
open Finset BooleanModule BooleanVertexExtension
open scoped BigOperators Pointwise

def Vertex : ℕ → Type
  | 0 => Fin 10
  | m+1 => BooleanVertexExtension.Vertex (Vertex m)

instance vertexFintype (m : ℕ) : Fintype (Vertex m) := by
  induction m with
  | zero => exact inferInstanceAs (Fintype (Fin 10))
  | succ m ih =>
    letI : Fintype (Vertex m) := ih
    exact inferInstanceAs (Fintype (Vertex m ⊕ Fin 1))

instance vertexDecidableEq (m : ℕ) : DecidableEq (Vertex m) := by
  induction m with
  | zero => exact inferInstanceAs (DecidableEq (Fin 10))
  | succ m ih =>
    letI : DecidableEq (Vertex m) := ih
    exact inferInstanceAs (DecidableEq (Vertex m ⊕ Fin 1))

def frame : (m : ℕ) → Vertex m × Vertex m × Vertex m
  | 0 => ((0 : Fin 10),(1 : Fin 10),(6 : Fin 10))
  | m+1 => (Sum.inl (frame m).2.1,Sum.inl (frame m).1,Sum.inr 0)

abbrev first (m : ℕ) : Vertex m := (frame m).1
abbrev second (m : ℕ) : Vertex m := (frame m).2.1
abbrev tip (m : ℕ) : Vertex m := (frame m).2.2

def graph : (m : ℕ) → SimpleGraph (Vertex m)
  | 0 => DiamondGeometry.graph
  | m+1 => SingleVertexGraph.graph (graph m) {first m,second m,tip m}

/-- The distinguished triangle has three different vertices at every step;
this fact depends only on the recursive graph presentation. -/
theorem frame_distinct (m : ℕ) :
    first m ≠ second m ∧ first m ≠ tip m ∧ second m ≠ tip m := by
  induction m with
  | zero =>
    change (0 : Fin 10) ≠ 1 ∧ (0 : Fin 10) ≠ 6 ∧ (1 : Fin 10) ≠ 6
    decide
  | succ m ih =>
    change (Sum.inl (second m) : Vertex m ⊕ Fin 1) ≠ Sum.inl (first m) ∧
      (Sum.inl (second m) : Vertex m ⊕ Fin 1) ≠ Sum.inr 0 ∧
      (Sum.inl (first m) : Vertex m ⊕ Fin 1) ≠ Sum.inr 0
    exact ⟨fun h => ih.1 (Sum.inl_injective h).symm,Sum.inl_ne_inr,Sum.inl_ne_inr⟩

def function : (m : ℕ) → SetFunction (Vertex m)
  | 0 => DiamondGeometry.function
  | m+1 => append (function m) (andOr (first m) (second m) (tip m))

theorem vertex_card (m : ℕ) : Fintype.card (Vertex m) = 10+m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change Fintype.card (Vertex m ⊕ Fin 1) = _
    rw [Fintype.card_sum,Fintype.card_fin,ih]
    omega

/-- The seed boundary is verified from the literal 57-clique polynomial,
using no private-kernel or rigidity premise. -/
theorem base_unit_boundary : UnitBoundary DiamondGeometry.function (0 : Fin 10) 1 6 := by
  refine ⟨by decide,by decide,by decide,?_⟩
  intro S h0 h6 h1
  rw [DiamondGeometry.delta_eq_slackZ (by decide) h0 h6]
  by_cases h2 : (2 : Fin 10) ∈ S <;>
    norm_num [DiamondGeometry.slackZ,DiamondGeometry.cliques,DiamondGeometry.coefficientsZ,
      Fin.sum_univ_succ,Finset.subset_iff,h0,h6,h1,h2]

theorem extreme_and_boundary (m : ℕ) :
    ExtremeSupermodular (function m) ∧ UnitBoundary (function m) (first m) (second m) (tip m) := by
  induction m with
  | zero => exact ⟨DiamondGeometry.extreme,base_unit_boundary⟩
  | succ m ih =>
    exact ⟨triangular_append_extreme ih.1 ih.2,triangular_append_boundary ih.2⟩

theorem extreme (m : ℕ) : ExtremeSupermodular (function m) := (extreme_and_boundary m).1
theorem unit_boundary (m : ℕ) : UnitBoundary (function m) (first m) (second m) (tip m) :=
  (extreme_and_boundary m).2

theorem frame_card (m : ℕ) : ({first m,second m,tip m} : Finset (Vertex m)).card = 3 := by
  have h := frame_distinct m
  simp [h.1,h.2.1,h.2.2]

theorem frame_clique (m : ℕ) : (graph m).IsClique ({first m,second m,tip m} : Finset (Vertex m)) := by
  induction m with
  | zero =>
    change DiamondGeometry.graph.IsClique ({0,1,6} : Finset (Fin 10))
    decide +kernel
  | succ m ih => exact triangular_append_triangle (unit_boundary m).1 ih

theorem graphical (m : ℕ) : Graphical (graph m) (function m) := by
  induction m with
  | zero => exact DiamondGeometry.graphical
  | succ m ih => exact triangular_append_graphical ih (frame_clique m)

theorem integerValued (m : ℕ) : IntegerValued (function m) := by
  induction m with
  | zero => exact DiamondGeometry.integerValued
  | succ m ih => exact append_integerValued ih (andOr_boolean _ _ _)

theorem elemental_upper (m : ℕ) :
    ∀ u v : Vertex m, u ≠ v → ∀ S, u ∉ S → v ∉ S →
      delta (function m) u v S ≤ (m+4 : ℕ) := by
  induction m with
  | zero =>
    intro u v huv S hu hv
    exact (DiamondGeometry.elemental_bounds huv hu hv).2
  | succ m ih =>
    have h := append_delta_upper (andOr_boolean (first m) (second m) (tip m))
      (Nat.cast_nonneg (m+4)) ih
    intro u v huv S hu hv
    have he : ((m+4 : ℕ) : ℝ)+1 = ((m+1+4 : ℕ) : ℝ) := by
      norm_num [Nat.cast_add] <;> ring
    simpa only [function,he] using h u v huv S hu hv

theorem positive_slack (m : ℕ) :
    ∀ u v : Vertex m, (graph m).Adj u v → ∃ S : Finset (Vertex m),
      u ∉ S ∧ v ∉ S ∧ 0 < delta (function m) u v S := by
  induction m with
  | zero => exact fun _ _ h => DiamondGeometry.positive_slack h
  | succ m ih => exact triangular_append_positive (unit_boundary m) ih

theorem connected (m : ℕ) : (graph m).Connected := by
  induction m with
  | zero => exact DiamondGeometry.graph_connected
  | succ m ih => exact SingleVertexGraph.connected ih ⟨first m,by simp⟩

theorem cliqueFree_five (m : ℕ) : (graph m).CliqueFree 5 := by
  induction m with
  | zero =>
    change DiamondGeometry.graph.CliqueFree 5
    intro C hC
    have hc : C.card = 5 := hC.card_eq
    obtain ⟨i,hi⟩ := DiamondGeometry.cliques_complete C ⟨by omega,hC.isClique⟩
    have hfour : ∀ i : Fin 57, (DiamondGeometry.cliques i).card ≤ 4 := by decide +kernel
    have hle := hfour i
    rw [hi] at hle
    omega
  | succ m ih =>
    exact SingleVertexGraph.cliqueFree_five ih
      (by simpa only [frame_card] using (show 3 ≤ 3 from le_rfl))

theorem edge_count (m : ℕ) : (edgeFamily (graph m)).card = 25+3*m := by
  induction m with
  | zero =>
    rw [graph,DiamondGeometry.edge_family_eq]
    decide +kernel
  | succ m ih =>
    rw [graph,SingleVertexGraph.edgeFamily_card,ih,frame_card]
    omega

theorem actual_summand (m : ℕ) : IsMinkowskiSummand (basePolytope (function m))
    (((m+4 : ℕ) : ℝ) • graphicalZonotope (graph m)) := by
  apply (isMinkowskiSummand_graphical_iff (extreme m).1.1 (extreme m).2.1
    (Nat.cast_nonneg (m+4))).mpr
  exact ⟨graphical m,fun u v huv _ S hu hv => elemental_upper m u v huv S hu hv⟩

theorem full_dimension (m : ℕ) : FullDimension (basePolytope (function m)) := by
  exact finrank_vectorSpan_eq_of_connected_slacks (extreme m).1.1 (extreme m).2.1
    (connected m) (fun u v huv => by
      obtain ⟨S,hu,hv,hp⟩ := positive_slack m u v huv
      exact ⟨S,hu,hv,ne_of_gt hp⟩)

theorem actual_direction_graph (m : ℕ) :
    actualDirectionGraph (basePolytope (function m)) = graph m := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  constructor
  · intro he
    obtain ⟨R,hR,hRc,hnR,hQR⟩ := actual_summand m
    exact basePolytope_summand_actualRootEdge (extreme m).1.1 (extreme m).2.1 (graph m)
      (Nat.cast_nonneg (m+4)) R hQR he
  · intro he
    obtain ⟨S,hu,hv,hp⟩ := positive_slack m u v he
    exact exposedSegment_of_positive_delta (extreme m).1.1 (extreme m).2.1 he.ne hu hv hp

theorem lattice (m : ℕ) : LatticePolytope (basePolytope (function m)) :=
  (integerValued m).basePolytope (extreme m).1.1 (extreme m).2.1

end SparseFamily
end GraphicalZonotopes
