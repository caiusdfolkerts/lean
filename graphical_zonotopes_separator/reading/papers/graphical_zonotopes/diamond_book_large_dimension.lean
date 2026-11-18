module

public import Papers.GraphicalZonotopes.DiamondGeometry
public import Papers.GraphicalZonotopes.DiamondBookGraph
public import Papers.GraphicalZonotopes.SetFunctionEmbeddingGeometry
public import Papers.GraphicalZonotopes.WeakSummandReduction

@[expose] public section
noncomputable section
namespace GraphicalZonotopes.DiamondBook
open Finset
open scoped Pointwise

def largeEmbedding (k : ℕ) (hk : 6≤k) : Fin 10 ↪ Vertex k where
  toFun x:=⟨x.val,by have:=x.isLt; omega⟩
  inj' x y h:=Fin.ext (congrArg (fun z : Vertex k => z.val) h)

theorem large_graph_comap (k : ℕ) (hk : 6≤k) :
    (graph k).comap (largeEmbedding k hk)=graph 6 := by
  apply SimpleGraph.ext
  funext x y
  rfl

theorem diamond_support_subgraph : DiamondGeometry.graph≤graph 6 := by
  change ∀ x y,DiamondGeometry.graph.Adj x y → (graph 6).Adj x y
  decide +kernel

theorem large_dimension_lower (k : ℕ) (hk : 6≤k) :
    9≤maximumIndecomposableDimension (graph k) := by
  let e:=largeEmbedding k hk
  let z:=SetFunctionEmbedding.extend e DiamondGeometry.function
  have hz : ExtremeSupermodular z:=SetFunctionEmbedding.extend_extreme e DiamondGeometry.extreme
  have hgraph0 : Graphical ((graph k).comap e) DiamondGeometry.function := by
    rw [large_graph_comap]
    exact DiamondGeometry.graphical.mono_graph diamond_support_subgraph
  have hgraph : Graphical (graph k) z:=SetFunctionEmbedding.extend_graphical e hgraph0
  have hd : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=9 := by
    rw [SetFunctionEmbedding.finrank_vectorSpan_extend e DiamondGeometry.normalized]
    exact DiamondGeometry.full_dimension
  have hfinite : IsFinitePolytope (basePolytope z):=
    (show IsGeneralizedPermutahedron (basePolytope z) from ⟨z,hz.1.1,hz.2.1,rfl⟩).finitePolytope
  have hle:=dimension_le_maximum hfinite hz.minkowskiIndecomposable
    ((isWeakMinkowskiSummand_graphical_iff hz.1.1 hz.2.1).mpr hgraph)
  rwa [hd] at hle

theorem diamond_witness :
    ∃ Q : Set (Fin 10 → ℝ),LatticePolytope Q ∧ MinkowskiIndecomposable Q ∧
      FullDimension Q ∧ IsMinkowskiSummand Q ((4 : ℝ) • graphicalZonotope (graph 6)) ∧
      directionCount Q=25 ∧ ¬HasAdmissibleSpanningThreeTree (graph 6) := by
  refine ⟨basePolytope DiamondGeometry.function,DiamondGeometry.lattice,
    DiamondGeometry.indecomposable,DiamondGeometry.full_dimension,?_,
    DiamondGeometry.direction_count,no_admissible_spanning_threeTree 6 (by norm_num)⟩
  apply (isMinkowskiSummand_graphical_iff DiamondGeometry.normalized.1
    DiamondGeometry.supermodular (by norm_num : (0 : ℝ)≤4)).mpr
  exact ⟨DiamondGeometry.graphical.mono_graph diamond_support_subgraph,
    fun _ _ huv _ _ hu hv => (DiamondGeometry.elemental_bounds huv hu hv).2⟩

end GraphicalZonotopes.DiamondBook
