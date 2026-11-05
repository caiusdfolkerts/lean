import cubical.pl.facet_connectivity
import cubical.colored_graph
import cubical.facet_determination

/-! # The actual facet cover of a cubical PL sphere -/

noncomputable section

namespace Cubical.PL.CubeComplex

open Classical Cubical.Bipartite

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] (K : CubeComplex V)

theorem vertex_in_facet {m : ℕ} (hK : K.IsSphere m) (v : V) :
    ∃ F : K.Facet m, v ∈ F.val.val := by
  obtain ⟨F, hF⟩ := K.cell_in_facet hK ⟨{v}, K.singleton_mem v⟩
  exact ⟨F, hF (Finset.mem_singleton_self v)⟩

theorem cell_neighbor (F : K.Cell) (hd : 1 ≤ K.dimension F.val)
    (v : V) (hv : v ∈ F.val) : ∃ w, w ∈ F.val ∧ K.graph.Adj v w := by
  let s := (K.cellVertex F).symm ⟨v, hv⟩
  let i : Fin (K.dimension F.val) := ⟨0, by omega⟩
  let w := K.cellVertex F (Cube.flip s i)
  refine ⟨w.val, w.property, ?_⟩
  have h := (K.chart_adj_iff F s (Cube.flip s i)).mpr ⟨i, rfl⟩
  simpa only [s, Equiv.apply_symm_apply] using h

/-- Cube matching across a codimension-one cell, transported through
the actual cell chart. -/
theorem cell_ridge_matching (F R : K.Cell) (hRF : R ≤ F)
    (hd : K.dimension R.val + 1 = K.dimension F.val)
    (v : V) (hvF : v ∈ F.val) (hvR : v ∉ R.val) :
    ∃ w, w ∈ R.val ∧ K.graph.Adj v w := by
  obtain ⟨s, A, hA⟩ := K.subfaces F.val F.property R.val R.property hRF
  change R.val = chartFace (K.cellVertex F) s A at hA
  have hcard : A.card + 1 = K.dimension F.val := by
    rw [hA, K.chart_face_dimension] at hd
    exact hd
  let x := (K.cellVertex F).symm ⟨v, hvF⟩
  have hx : x ∉ Cube.FaceAt s A := by
    intro hx
    apply hvR
    rw [hA]
    exact (mem_chartFace (K.cellVertex F) s A ⟨v, hvF⟩).mpr
      ((mem_coordinateFace s x A).mpr hx)
  obtain ⟨y, hy, hxy⟩ := Cube.ridge_matching s x A hcard hx
  refine ⟨(K.cellVertex F y).val, ?_, ?_⟩
  · rw [hA]
    apply (mem_chartFace (K.cellVertex F) s A (K.cellVertex F y)).mpr
    simpa only [Equiv.symm_apply_apply, mem_coordinateFace] using hy
  · have h := (K.chart_adj_iff F x y).mpr hxy
    simpa only [x, Equiv.apply_symm_apply] using h

theorem facet_crossing {m : ℕ} (F G : K.Facet m)
    (hFG : K.facetStep m F G) (v : V) (hvG : v ∈ G.val.val) (hvF : v ∉ F.val.val) :
    ∃ w, w ∈ F.val.val ∧ K.graph.Adj v w := by
  obtain ⟨R, hRF, hRG, hdR⟩ := hFG
  obtain ⟨w, hw, hvw⟩ := K.cell_ridge_matching G.val R hRG
    (hdR.trans G.property.symm) v hvG (fun h => hvF (hRF h))
  exact ⟨w, hRF hw, hvw⟩

/-- This cover contains the original vertices, original edges and
maximal cubical cells. Its connectivity is a proved PL-topological fact. -/
def cubicalFacetCover {m : ℕ} (hK : K.IsSphere m) (hm : 1 ≤ m)
    (c : K.graph.Coloring Bool) : Cubical.FacetCover (black c) (white c) (K.Facet m) where
  blackMem F b := b.val ∈ F.val.val
  whiteMem F w := w.val ∈ F.val.val
  edgeMem F e := e.val.1.val ∈ F.val.val ∧ e.val.2.val ∈ F.val.val
  edgeBlack _ _ h := h.1
  edgeWhite _ _ h := h.2
  coverBlack b := K.vertex_in_facet hK b.val
  coverWhite w := K.vertex_in_facet hK w.val
  whiteIncident F w hw := by
    obtain ⟨b, hbF, hwb⟩ := K.cell_neighbor F.val (by rw [F.property]; exact hm) w.val hw
    let b' : Black c := ⟨b, color_black_of_adj_white c w hwb⟩
    exact ⟨⟨(b', w), hwb.symm⟩, ⟨hbF, hw⟩, rfl⟩
  step := K.facetStep m
  connected := K.facetStep_connected hK hm
  crossing F G hFG b hb := by
    by_cases hbF : b.val ∈ F.val.val
    · exact Or.inl hbF
    · obtain ⟨w, hwF, hbw⟩ := K.facet_crossing F G hFG b.val hb hbF
      let w' : White c := ⟨w, color_white_of_adj_black c b hbw⟩
      exact Or.inr ⟨⟨(b, w'), hbw⟩, rfl, hwF⟩

end Cubical.PL.CubeComplex
