import cubical.pl.facet_cover

/-! # The original vertex and edge counts of a cubical complex -/

noncomputable section

namespace Cubical.PL.CubeComplex

open Classical Cubical.Bipartite

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] (K : CubeComplex V)

/-- Number of actual cells of dimension `i`, counted without multiplicity. -/
def faceNumber (i : ℕ) : ℕ := Fintype.card {F : K.Cell // K.dimension F.val = i}

def vertexCellEquiv : V ≃ {F : K.Cell // K.dimension F.val = 0} :=
  Equiv.ofBijective (fun v => ⟨⟨{v}, K.singleton_mem v⟩, K.singleton_dimension v⟩)
    ⟨by
      intro v w h
      exact Finset.singleton_injective (congrArg (fun F => F.val.val) h),
    by
      intro F
      have hc := K.cell_vertex_card F.val
      rw [F.property, pow_zero] at hc
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc
      exact ⟨v, Subtype.ext (Subtype.ext hv.symm)⟩⟩

@[simp] theorem faceNumber_zero : K.faceNumber 0 = Fintype.card V :=
  (Fintype.card_congr K.vertexCellEquiv).symm

def edgeCell (c : K.graph.Coloring Bool) (e : Edge c) :
    {F : K.Cell // K.dimension F.val = 1} :=
  ⟨⟨{e.val.1.val, e.val.2.val}, e.property.2.1⟩, e.property.2.2⟩

theorem edgeCell_injective (c : K.graph.Coloring Bool) : Function.Injective (K.edgeCell c) := by
  intro e f h
  have heq : {e.val.1.val, e.val.2.val} = {f.val.1.val, f.val.2.val} :=
    congrArg (fun F => F.val.val) h
  have hb : e.val.1.val = f.val.1.val := by
    have hm : e.val.1.val ∈ ({f.val.1.val, f.val.2.val} : Finset V) := by rw [← heq]; simp
    rcases Finset.mem_insert.mp hm with h | h
    · exact h
    · have hc := congrArg c (Finset.mem_singleton.mp h)
      rw [e.val.1.property, f.val.2.property] at hc
      cases hc
  have hw : e.val.2.val = f.val.2.val := by
    have hm : e.val.2.val ∈ ({f.val.1.val, f.val.2.val} : Finset V) := by rw [← heq]; simp
    rcases Finset.mem_insert.mp hm with h | h
    · have hc := congrArg c h
      rw [e.val.2.property, f.val.1.property] at hc
      cases hc
    · exact Finset.mem_singleton.mp h
  exact Subtype.ext (Prod.ext (Subtype.ext hb) (Subtype.ext hw))

theorem edgeCell_surjective (c : K.graph.Coloring Bool) : Function.Surjective (K.edgeCell c) := by
  intro F
  have hc := K.cell_vertex_card F.val
  rw [F.property, pow_one] at hc
  obtain ⟨v, w, hvw, hF⟩ := Finset.card_eq_two.mp hc
  have hadj : K.graph.Adj v w := ⟨hvw, hF ▸ F.val.property, hF ▸ F.property⟩
  cases hv : c v with
  | false =>
    let b : Black c := ⟨v, hv⟩
    let a : White c := ⟨w, color_white_of_adj_black c b hadj⟩
    exact ⟨⟨(b, a), hadj⟩, Subtype.ext (Subtype.ext hF.symm)⟩
  | true =>
    let a : White c := ⟨v, hv⟩
    let b : Black c := ⟨w, color_black_of_adj_white c a hadj⟩
    refine ⟨⟨(b, a), hadj.symm⟩, Subtype.ext (Subtype.ext ?_)⟩
    exact (Finset.pair_comm w v).trans hF.symm

def edgeCellEquiv (c : K.graph.Coloring Bool) :
    Edge c ≃ {F : K.Cell // K.dimension F.val = 1} :=
  Equiv.ofBijective (K.edgeCell c) ⟨K.edgeCell_injective c, K.edgeCell_surjective c⟩

theorem card_edges (c : K.graph.Coloring Bool) : Fintype.card (Edge c) = K.faceNumber 1 :=
  Fintype.card_congr (K.edgeCellEquiv c)

theorem nonempty_vertices {m : ℕ} (hK : K.IsSphere m) : Nonempty V := by
  obtain ⟨x, hx⟩ := hK.nonempty
  obtain ⟨s, hs, _⟩ := K.realization.mem_space_iff.mp hx
  obtain ⟨C, hC, _⟩ := hs
  obtain ⟨F, _⟩ := hC.1
  obtain ⟨v, _⟩ := K.nonempty F.val F.property
  exact ⟨v⟩

theorem nonempty_facets {m : ℕ} (hK : K.IsSphere m) : Nonempty (K.Facet m) := by
  obtain ⟨v⟩ := K.nonempty_vertices hK
  obtain ⟨F, _⟩ := K.vertex_in_facet hK v
  exact ⟨F⟩

end Cubical.PL.CubeComplex
