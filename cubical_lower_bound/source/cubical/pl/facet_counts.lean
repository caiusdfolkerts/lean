import cubical.pl.facet_cover

/-!
# Exact color and edge counts in cubical cells

The counts use the actual cube charts.  In particular they apply to the
original facet cover of every cubical PL sphere, with no regularity or
incidence-count hypotheses added to the topological assumptions.
-/

noncomputable section

namespace Cubical.PL.CubeComplex

open Classical Cubical.Bipartite

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] (K : CubeComplex V)

theorem cube_color_cards_pos {d : ℕ} (hd : 1 ≤ d)
    (c : Cube.Vertex d → Bool) (hc : Cube.ProperColoring c) :
    Fintype.card (Cube.Black c) = 2 ^ (d - 1) ∧
      Fintype.card (Cube.White c) = 2 ^ (d - 1) := by
  cases d with
  | zero => omega
  | succ d => simpa using Cube.card_colors c hc

def cellColors (c : K.graph.Coloring Bool) (F : K.Cell) :
    Cube.Vertex (K.dimension F.val) → Bool := fun s => c (K.cellVertex F s).val

theorem cellColors_proper (c : K.graph.Coloring Bool) (F : K.Cell) :
    Cube.ProperColoring (K.cellColors c F) := by
  intro s i
  exact color_eq_not_of_adj c ((K.chart_adj_iff F s (Cube.flip s i)).mpr ⟨i, rfl⟩)

def cellBlackEquiv (c : K.graph.Coloring Bool) (F : K.Cell) :
    {b : Black c // b.val ∈ F.val} ≃ Cube.Black (K.cellColors c F) where
  toFun b := ⟨(K.cellVertex F).symm ⟨b.val.val, b.property⟩, by
    simpa only [cellColors, Equiv.apply_symm_apply] using b.val.property⟩
  invFun s := ⟨⟨(K.cellVertex F s.val).val, s.property⟩, (K.cellVertex F s.val).property⟩
  left_inv b := by
    apply Subtype.ext
    apply Subtype.ext
    change (K.cellVertex F ((K.cellVertex F).symm ⟨b.val.val, b.property⟩)).val = b.val.val
    exact congrArg Subtype.val ((K.cellVertex F).apply_symm_apply _)
  right_inv s := Subtype.ext ((K.cellVertex F).symm_apply_apply _)

def cellWhiteEquiv (c : K.graph.Coloring Bool) (F : K.Cell) :
    {w : White c // w.val ∈ F.val} ≃ Cube.White (K.cellColors c F) where
  toFun w := ⟨(K.cellVertex F).symm ⟨w.val.val, w.property⟩, by
    simpa only [cellColors, Equiv.apply_symm_apply] using w.val.property⟩
  invFun s := ⟨⟨(K.cellVertex F s.val).val, s.property⟩, (K.cellVertex F s.val).property⟩
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    change (K.cellVertex F ((K.cellVertex F).symm ⟨w.val.val, w.property⟩)).val = w.val.val
    exact congrArg Subtype.val ((K.cellVertex F).apply_symm_apply _)
  right_inv s := Subtype.ext ((K.cellVertex F).symm_apply_apply _)

theorem cell_color_cards (c : K.graph.Coloring Bool) (F : K.Cell)
    (hd : 1 ≤ K.dimension F.val) :
    Fintype.card {b : Black c // b.val ∈ F.val} = 2 ^ (K.dimension F.val - 1) ∧
      Fintype.card {w : White c // w.val ∈ F.val} = 2 ^ (K.dimension F.val - 1) := by
  have h := cube_color_cards_pos hd (K.cellColors c F) (K.cellColors_proper c F)
  exact ⟨(Fintype.card_congr (K.cellBlackEquiv c F)).trans h.1,
    (Fintype.card_congr (K.cellWhiteEquiv c F)).trans h.2⟩

def cellNeighborEquiv (F : K.Cell) (v : V) (hv : v ∈ F.val) :
    Fin (K.dimension F.val) ≃ {a : V // a ∈ F.val ∧ K.graph.Adj v a} :=
  Equiv.ofBijective
    (fun i => ⟨(K.cellVertex F (Cube.flip ((K.cellVertex F).symm ⟨v, hv⟩) i)).val,
      (K.cellVertex F _).property, by
        have h := (K.chart_adj_iff F ((K.cellVertex F).symm ⟨v, hv⟩)
          (Cube.flip ((K.cellVertex F).symm ⟨v, hv⟩) i)).mpr ⟨i, rfl⟩
        simpa only [Equiv.apply_symm_apply] using h⟩)
    ⟨by
      intro i j h
      apply Cube.flip_index_injective ((K.cellVertex F).symm ⟨v, hv⟩)
      apply (K.cellVertex F).injective
      apply Subtype.ext
      exact congrArg (fun x : {a : V // a ∈ F.val ∧ K.graph.Adj v a} => x.val) h, by
      intro a
      have h : (Cube.graph (K.dimension F.val)).Adj
          ((K.cellVertex F).symm ⟨v, hv⟩) ((K.cellVertex F).symm ⟨a.val, a.property.1⟩) := by
        apply (K.chart_adj_iff F _ _).mp
        simpa only [Equiv.apply_symm_apply] using a.property.2
      obtain ⟨i, hi⟩ := h
      refine ⟨i, Subtype.ext ?_⟩
      change (K.cellVertex F (Cube.flip ((K.cellVertex F).symm ⟨v, hv⟩) i)).val = a.val
      rw [← hi]
      exact congrArg Subtype.val ((K.cellVertex F).apply_symm_apply _)⟩

theorem cell_neighbor_card (F : K.Cell) (v : V) (hv : v ∈ F.val) :
    Fintype.card {a : V // a ∈ F.val ∧ K.graph.Adj v a} = K.dimension F.val := by
  rw [← Fintype.card_congr (K.cellNeighborEquiv F v hv), Fintype.card_fin]

theorem facet_color_cards {m : ℕ} (c : K.graph.Coloring Bool) (F : K.Facet m)
    (hm : 1 ≤ m) :
    Fintype.card {b : Black c // b.val ∈ F.val.val} = 2 ^ (m - 1) ∧
      Fintype.card {w : White c // w.val ∈ F.val.val} = 2 ^ (m - 1) := by
  simpa only [F.property] using K.cell_color_cards c F.val (by rw [F.property]; exact hm)

def facetEdgeNeighborEquiv {m : ℕ} (hK : K.IsSphere m) (hm : 1 ≤ m)
    (c : K.graph.Coloring Bool) (F : K.Facet m)
    (b : {b : Black c // (K.cubicalFacetCover hK hm c).blackMem F b}) :
    {e : {e : Edge c // (K.cubicalFacetCover hK hm c).edgeMem F e} //
      (K.cubicalFacetCover hK hm c).facetBlack F e = b} ≃
    {a : V // a ∈ F.val.val ∧ K.graph.Adj b.val.val a} where
  toFun e := ⟨e.val.val.val.2.val, e.val.property.2, by
    have hb := congrArg
      (fun x : {b : Black c // (K.cubicalFacetCover hK hm c).blackMem F b} => x.val.val)
      e.property
    change e.val.val.val.1.val = b.val.val at hb
    rw [← hb]
    exact e.val.val.property⟩
  invFun a := ⟨⟨⟨(b.val, ⟨a.val, color_white_of_adj_black c b.val a.property.2⟩),
    a.property.2⟩, ⟨b.property, a.property.1⟩⟩, rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (congrArg Subtype.val e.property).symm rfl
  right_inv _ := rfl

theorem facet_black_degree {m : ℕ} (hK : K.IsSphere m) (hm : 1 ≤ m)
    (c : K.graph.Coloring Bool) (F : K.Facet m)
    (b : {b : Black c // (K.cubicalFacetCover hK hm c).blackMem F b}) :
    Fintype.card {e : {e : Edge c // (K.cubicalFacetCover hK hm c).edgeMem F e} //
      (K.cubicalFacetCover hK hm c).facetBlack F e = b} = m := by
  rw [Fintype.card_congr (K.facetEdgeNeighborEquiv hK hm c F b)]
  exact (K.cell_neighbor_card F.val b.val.val b.property).trans F.property

theorem facet_edges_card {m : ℕ} (hK : K.IsSphere m) (hm : 1 ≤ m)
    (c : K.graph.Coloring Bool) (F : K.Facet m) :
    Fintype.card {e : Edge c // (K.cubicalFacetCover hK hm c).edgeMem F e} =
      m * 2 ^ (m - 1) := by
  let C := K.cubicalFacetCover hK hm c
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (C.facetBlack F)), Fintype.card_sigma]
  dsimp only [C]
  simp_rw [K.facet_black_degree hK hm c F]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hc : Nat.card {b : Black c // (K.cubicalFacetCover hK hm c).blackMem F b} =
      2 ^ (m - 1) := by
    change Nat.card {b : Black c // b.val ∈ F.val.val} = _
    rw [Nat.card_eq_fintype_card]
    exact (K.facet_color_cards c F hm).1
  rw [← Nat.card_eq_fintype_card, hc]
  exact Nat.mul_comm _ _

theorem facet_whiteEndpoint_injective {m : ℕ} (hK : K.IsSphere m) (hm : 1 ≤ m)
    (c : K.graph.Coloring Bool) (F : K.Facet m)
    (b : {b : Black c // (K.cubicalFacetCover hK hm c).blackMem F b}) :
    Function.Injective (fun e :
      {e : {e : Edge c // (K.cubicalFacetCover hK hm c).edgeMem F e} //
        (K.cubicalFacetCover hK hm c).facetBlack F e = b} =>
      (K.cubicalFacetCover hK hm c).facetWhite F e.val) := by
  intro e e' h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (congrArg Subtype.val (e.property.trans e'.property.symm))
    (congrArg Subtype.val h)

theorem facet_global_whiteEndpoint_injective {m : ℕ}
    (hK : K.IsSphere m) (hm : 1 ≤ m) (c : K.graph.Coloring Bool) (F : K.Facet m)
    (b : {b : Black c // (K.cubicalFacetCover hK hm c).blackMem F b}) :
    Function.Injective (fun e :
      {e : {e : Edge c // (K.cubicalFacetCover hK hm c).edgeMem F e} //
        (K.cubicalFacetCover hK hm c).facetBlack F e = b} => white c e.val.val) := by
  intro e e' h
  exact K.facet_whiteEndpoint_injective hK hm c F b (Subtype.ext h)

end Cubical.PL.CubeComplex
