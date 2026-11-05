import cubical.pl.neighbor_link
import cubical.pl.facet_cover
import cubical.abstract_bound

/-!
# Square stars in genuine abstract cubical complexes

All labels are original vertices, edges and square cells.  In particular,
opposite labels are injective because two cells meet in a common face.
-/

noncomputable section

open Classical
attribute [local instance] Classical.propDecidable

namespace Cubical.PL.CubeComplex

open Cubical.Bipartite

variable {V : Type*} [Fintype V] [DecidableEq V] (K : CubeComplex V)

abbrev TwoCellAt (v : V) := {F : K.Cell // K.dimension F.val = 2 ∧ v ∈ F.val}

structure SquareCorners (v : V) (F : K.TwoCellAt v) where
  left : K.Neighbor v
  right : K.Neighbor v
  left_mem : left.val ∈ F.val.val
  right_mem : right.val ∈ F.val.val
  left_ne_right : left ≠ right
  opposite : V
  opposite_ne : opposite ≠ v
  opposite_mem : opposite ∈ F.val.val
  left_adj : K.graph.Adj left.val opposite
  right_adj : K.graph.Adj right.val opposite
  all_neighbors : ∀ a : K.Neighbor v, a.val ∈ F.val.val → a = left ∨ a = right

theorem squareCorners_nonempty (v : V) (F : K.TwoCellAt v) :
    Nonempty (K.SquareCorners v F) := by
  have hcard : (K.neighborFace F.val.val v).card = 2 :=
    (K.neighborFace_card F.val v F.property.2).trans F.property.1
  obtain ⟨a, b, hab, habset⟩ := Finset.card_eq_two.mp hcard
  have ha : a ∈ F.val.val ∧ K.graph.Adj v a := by
    apply (K.mem_neighborFace _ _ _).mp
    rw [habset]
    simp
  have hb : b ∈ F.val.val ∧ K.graph.Adj v b := by
    apply (K.mem_neighborFace _ _ _).mp
    rw [habset]
    simp
  let φ := K.cellVertex F.val
  let s := φ.symm ⟨v, F.property.2⟩
  let t := φ.symm ⟨a, ha.1⟩
  let u := φ.symm ⟨b, hb.1⟩
  have hst : (Cube.graph (K.dimension F.val.val)).Adj s t := by
    apply (K.chart_adj_iff F.val s t).mp
    simpa only [s, t, φ, Equiv.apply_symm_apply] using ha.2
  have hsu : (Cube.graph (K.dimension F.val.val)).Adj s u := by
    apply (K.chart_adj_iff F.val s u).mp
    simpa only [s, u, φ, Equiv.apply_symm_apply] using hb.2
  have htu : t ≠ u := by
    intro h
    exact hab (congrArg Subtype.val (φ.symm.injective h))
  obtain ⟨z, hz, hzs, htz, huz, _⟩ := Cube.square_completion s t u Finset.univ
    (by simp [F.property.1]) (by simp [Cube.FaceAt]) (by simp [Cube.FaceAt]) hst hsu htu
  refine ⟨{
    left := ⟨a, ha.2⟩
    right := ⟨b, hb.2⟩
    left_mem := ha.1
    right_mem := hb.1
    left_ne_right := fun h => hab (congrArg Subtype.val h)
    opposite := (φ z).val
    opposite_ne := ?_
    opposite_mem := (φ z).property
    left_adj := ?_
    right_adj := ?_
    all_neighbors := ?_ }⟩
  · intro h
    apply hzs
    have h' : φ z = (⟨v, F.property.2⟩ : F.val.val) := Subtype.ext h
    exact (φ.eq_symm_apply).mpr h'
  · have h := (K.chart_adj_iff F.val t z).mpr htz
    simpa only [t, φ, Equiv.apply_symm_apply] using h
  · have h := (K.chart_adj_iff F.val u z).mpr huz
    simpa only [u, φ, Equiv.apply_symm_apply] using h
  · intro w hw
    have hmem : w.val ∈ K.neighborFace F.val.val v :=
      (K.mem_neighborFace _ _ _).mpr ⟨hw, w.property⟩
    rw [habset] at hmem
    rcases Finset.mem_insert.mp hmem with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext (Finset.mem_singleton.mp h))

def squareCorners (v : V) (F : K.TwoCellAt v) : K.SquareCorners v F :=
  Classical.choice (K.squareCorners_nonempty v F)

theorem two_cells_eq_of_nonadjacent (F G : K.Cell)
    (hF : K.dimension F.val = 2) (hG : K.dimension G.val = 2)
    (v w : V) (hvF : v ∈ F.val) (hwF : w ∈ F.val)
    (hvG : v ∈ G.val) (hwG : w ∈ G.val) (hvw : v ≠ w)
    (hnadj : ¬ K.graph.Adj v w) : F = G := by
  let H : K.Cell := ⟨F.val ∩ G.val, K.inter_mem F.val F.property G.val G.property
    ⟨v, Finset.mem_inter.mpr ⟨hvF, hvG⟩⟩⟩
  have hvH : v ∈ H.val := Finset.mem_inter.mpr ⟨hvF, hvG⟩
  have hwH : w ∈ H.val := Finset.mem_inter.mpr ⟨hwF, hwG⟩
  have hHF : H ≤ F := Finset.inter_subset_left
  have hHG : H ≤ G := Finset.inter_subset_right
  have hdim : K.dimension H.val = 2 := by
    have hle : K.dimension H.val ≤ 2 := (K.dimension_mono H F hHF).trans_eq hF
    have hpair : {v, w} ⊆ H.val :=
      Finset.insert_subset_iff.mpr ⟨hvH, Finset.singleton_subset_iff.mpr hwH⟩
    have hcard : 2 ≤ H.val.card := by
      simpa [hvw] using Finset.card_le_card hpair
    by_contra hne
    have hdimle : K.dimension H.val ≤ 1 := by omega
    have hdimone : K.dimension H.val = 1 := by
      rw [K.cell_vertex_card H] at hcard
      by_contra hdne
      have hz : K.dimension H.val = 0 := by omega
      simp [hz] at hcard
    have heq : {v, w} = H.val := by
      apply Finset.eq_of_subset_of_card_le hpair
      rw [K.cell_vertex_card H, hdimone]
      simp [hvw]
    apply hnadj
    exact ⟨hvw, heq.symm ▸ H.property, by rw [heq]; exact hdimone⟩
  have hEF := (K.dimension_eq_iff_eq H F hHF).mp (hdim.trans hF.symm)
  have hEG := (K.dimension_eq_iff_eq H G hHG).mp (hdim.trans hG.symm)
  exact hEF.symm.trans hEG

def coloredNeighbor (c : K.graph.Coloring Bool) (w : White c)
    (a : K.Neighbor w.val) : Black c :=
  ⟨a.val, color_black_of_adj_white c w a.property⟩

def squareOpposite (c : K.graph.Coloring Bool) (w : White c)
    (F : K.TwoCellAt w.val) : White c :=
  ⟨(K.squareCorners w.val F).opposite,
    color_white_of_adj_black c (K.coloredNeighbor c w (K.squareCorners w.val F).left)
      (K.squareCorners w.val F).left_adj⟩

theorem squareOpposite_ne_center (c : K.graph.Coloring Bool) (w : White c)
    (F : K.TwoCellAt w.val) : K.squareOpposite c w F ≠ w := by
  intro h
  exact (K.squareCorners w.val F).opposite_ne (congrArg Subtype.val h)

theorem squareOpposite_injective (c : K.graph.Coloring Bool) (w : White c) :
    Function.Injective (K.squareOpposite c w) := by
  intro F G hFG
  let z := (K.squareOpposite c w F).val
  have hzG : z ∈ G.val.val := by
    change (K.squareOpposite c w F).val ∈ G.val.val
    rw [hFG]
    exact (K.squareCorners w.val G).opposite_mem
  have hnadj : ¬ K.graph.Adj w.val z := by
    intro h
    exact c.valid h (w.property.trans (K.squareOpposite c w F).property.symm)
  apply Subtype.ext
  exact K.two_cells_eq_of_nonadjacent F.val G.val F.property.1 G.property.1
    w.val z F.property.2 (K.squareCorners w.val F).opposite_mem G.property.2 hzG
    (K.squareCorners w.val F).opposite_ne.symm hnadj

theorem squareCorners_cover_link_edge (v : V) (a b : K.Neighbor v)
    (hab : (K.neighborGraph v).Adj a b) :
    ∃ F : K.TwoCellAt v,
      ((K.squareCorners v F).left = a ∧ (K.squareCorners v F).right = b) ∨
      ((K.squareCorners v F).left = b ∧ (K.squareCorners v F).right = a) := by
  obtain ⟨hne, F, hvF, hdF, hpair⟩ := (K.neighborGraph_adj_iff v a b).mp hab
  let F' : K.TwoCellAt v := ⟨F, hdF, hvF⟩
  let S := K.squareCorners v F'
  have ha : a.val ∈ F.val := (K.mem_neighborSimplex F v a).mp (by rw [hpair]; simp)
  have hb : b.val ∈ F.val := (K.mem_neighborSimplex F v b).mp (by rw [hpair]; simp)
  have ha' := S.all_neighbors a ha
  have hb' := S.all_neighbors b hb
  refine ⟨F', ?_⟩
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
  · exact (hne (ha'.trans hb'.symm)).elim
  · exact Or.inl ⟨ha'.symm, hb'.symm⟩
  · exact Or.inr ⟨hb'.symm, ha'.symm⟩
  · exact (hne (ha'.trans hb'.symm)).elim

abbrev FacetPins {m : ℕ} (f : K.Facet m) (v : V) :=
  {a : K.Neighbor v // a.val ∈ f.val.val}

def cubicalStarData {m : ℕ} (c : K.graph.Coloring Bool) (f : K.Facet m) (w : White c) :
    Cubical.StarData (black c) (white c) (K.Neighbor w.val)
      (K.TwoCellAt w.val) (K.FacetPins f w.val) where
  center := w
  neighbor := K.coloredNeighbor c w
  centralEdge a := ⟨(K.coloredNeighbor c w a, w), a.property.symm⟩
  centralBlack _ := rfl
  centralWhite _ := rfl
  left F := (K.squareCorners w.val F).left
  right F := (K.squareCorners w.val F).right
  opposite := K.squareOpposite c w
  leftEdge F := ⟨(K.coloredNeighbor c w (K.squareCorners w.val F).left,
    K.squareOpposite c w F), (K.squareCorners w.val F).left_adj⟩
  rightEdge F := ⟨(K.coloredNeighbor c w (K.squareCorners w.val F).right,
    K.squareOpposite c w F), (K.squareCorners w.val F).right_adj⟩
  leftBlack _ := rfl
  rightBlack _ := rfl
  leftWhite _ := rfl
  rightWhite _ := rfl
  pin := Subtype.val

def cubicalStarCover {m : ℕ} (hK : K.IsSphere m) (hm : 1 ≤ m)
    (c : K.graph.Coloring Bool) :
    (K.cubicalFacetCover hK hm c).StarCover
      (fun j => K.Neighbor j.val.2.val)
      (fun j => K.TwoCellAt j.val.2.val)
      (fun j => K.FacetPins j.val.1 j.val.2.val) where
  star j := K.cubicalStarData c j.val.1 j.val.2
  center _ := rfl
  covers j e he := by
    have hwhite : white c e = j.val.2 := he
    have hadj : K.graph.Adj j.val.2.val (black c e).val := by
      rw [← hwhite]
      exact e.property.symm
    exact ⟨⟨(black c e).val, hadj⟩, rfl⟩
  pinMem _ t := t.property
  link j := K.neighborGraph j.val.2.val
  linkEdges j a b hab := K.squareCorners_cover_link_edge j.val.2.val a b hab
  pin_injective _ := Subtype.val_injective
  opposite_injective j := K.squareOpposite_injective c j.val.2
  opposite_ne_center j := K.squareOpposite_ne_center c j.val.2

theorem facetPins_card {m : ℕ} (f : K.Facet m) (v : V) (hv : v ∈ f.val.val) :
    Fintype.card (K.FacetPins f v) = m := by
  let e : K.FacetPins f v ≃ K.neighborFace f.val.val v := {
    toFun a := ⟨a.val.val, (K.mem_neighborFace _ _ _).mpr ⟨a.property, a.val.property⟩⟩
    invFun a := ⟨⟨a.val, ((K.mem_neighborFace _ _ _).mp a.property).2⟩,
      ((K.mem_neighborFace _ _ _).mp a.property).1⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Fintype.card_congr e, Fintype.card_coe, K.neighborFace_card f.val v hv, f.property]

end Cubical.PL.CubeComplex
