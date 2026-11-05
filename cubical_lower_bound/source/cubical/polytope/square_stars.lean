import cubical.polytope.facet_cover
import cubical.polytope.face_incidence
import cubical.polytope.two_faces
import cubical.abstract_bound

/-! # The square-star incidence data in the local propagation lemma

Every row is attached to an actual edge or two-face. Opposite-vertex labels
are proved distinct using the geometric intersection property of faces.
-/

open Set Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope Cubical.Bipartite

variable {n : ℕ} {P : ConvexPolytope n}

def neighborLinkGraph (v : VertexType P) : SimpleGraph (NeighborOf v) where
  Adj a b := a ≠ b ∧ ∃ F : Set (E n), P.IsFace F ∧ faceDim F = 2 ∧
    v.val ∈ F ∧ a.val.val ∈ F ∧ b.val.val ∈ F
  symm := by
    constructor
    rintro a b ⟨hne, F, hF, hdF, hv, ha, hb⟩
    exact ⟨hne.symm, F, hF, hdF, hv, hb, ha⟩
  loopless := by
    constructor
    intro a h
    exact h.1 rfl

def DatiFetta.neighborGraphIso {v : VertexType P} (D : DatiFetta P v.val) :
    neighborLinkGraph v ≃g polytopeGraph D.politopo where
  __ := D.neighborEquiv
  map_rel_iff' := by
    intro a b
    exact D.neighborEquiv_adj_iff a b

structure SquareCorners (v : VertexType P) (F : IncidentFaceType P v 2) where
  left : NeighborOf v
  right : NeighborOf v
  left_mem : left.val.val ∈ F.val.val
  right_mem : right.val.val ∈ F.val.val
  left_ne_right : left ≠ right
  opposite : VertexType P
  opposite_ne : opposite ≠ v
  opposite_mem : opposite.val ∈ F.val.val
  left_adj : (polytopeGraph P).Adj left.val opposite
  right_adj : (polytopeGraph P).Adj right.val opposite
  all_neighbors : ∀ a : NeighborOf v, a.val.val ∈ F.val.val → a = left ∨ a = right

theorem IsCubical.squareCorners_nonempty (hc : IsCubical P) (hdim : 3 ≤ P.dim)
    (v : VertexType P) (F : IncidentFaceType P v 2) : Nonempty (SquareCorners v F) := by
  have hdF := F.property.1
  have hcard := hc.face_neighbor_card P (by omega) F.val.property (by omega)
    v F.property.2
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by rw [hcard, hdF]; omega)
  have hab' : a.val ≠ b.val := fun h => hab (Subtype.ext h)
  obtain ⟨z, hzv, hzF, haz, hbz, hall⟩ := hc.square_corners P hdim
    F.val.val F.val.property hdF v a.val b.val F.property.2
    a.property.1 b.property.1 a.property.2 b.property.2 hab'
  refine ⟨{
    left := ⟨a.val, a.property.2⟩
    right := ⟨b.val, b.property.2⟩
    left_mem := a.property.1
    right_mem := b.property.1
    left_ne_right := fun h => hab' (congrArg (fun x : NeighborOf v => x.val) h)
    opposite := z
    opposite_ne := hzv
    opposite_mem := hzF
    left_adj := haz
    right_adj := hbz
    all_neighbors := ?_ }⟩
  intro u hu
  rcases hall u.val hu u.property with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

def IsCubical.squareCorners (hc : IsCubical P) (hdim : 3 ≤ P.dim)
    (v : VertexType P) (F : IncidentFaceType P v 2) : SquareCorners v F :=
  Classical.choice (hc.squareCorners_nonempty hdim v F)

def coloredNeighbor (c : (polytopeGraph P).Coloring Bool) (w : White c)
    (a : NeighborOf w.val) : Black c :=
  ⟨a.val, color_black_of_adj_white c w a.property⟩

def squareOpposite (hc : IsCubical P) (hdim : 3 ≤ P.dim)
    (c : (polytopeGraph P).Coloring Bool) (w : White c)
    (F : IncidentFaceType P w.val 2) : White c :=
  ⟨(hc.squareCorners hdim w.val F).opposite,
    color_white_of_adj_black c
      (coloredNeighbor c w (hc.squareCorners hdim w.val F).left)
      (hc.squareCorners hdim w.val F).left_adj⟩

theorem squareOpposite_ne_center (hc : IsCubical P) (hdim : 3 ≤ P.dim)
    (c : (polytopeGraph P).Coloring Bool) (w : White c)
    (F : IncidentFaceType P w.val 2) : squareOpposite hc hdim c w F ≠ w := by
  intro h
  exact (hc.squareCorners hdim w.val F).opposite_ne (congrArg Subtype.val h)

theorem squareOpposite_injective (hc : IsCubical P) (hdim : 3 ≤ P.dim)
    (c : (polytopeGraph P).Coloring Bool) (w : White c) :
    Function.Injective (squareOpposite hc hdim c w) := by
  intro F G hFG
  let z := (squareOpposite hc hdim c w F).val
  have hzG : z.val ∈ G.val.val := by
    change (squareOpposite hc hdim c w F).val.val ∈ G.val.val
    rw [hFG]
    exact (hc.squareCorners hdim w.val G).opposite_mem
  have hne : w.val ≠ z := (hc.squareCorners hdim w.val F).opposite_ne.symm
  have hnadj : ¬ (polytopeGraph P).Adj w.val z := by
    intro hwz
    have hbad := c.valid hwz
    exact hbad (w.property.trans (squareOpposite hc hdim c w F).property.symm)
  have hfaces := two_faces_eq_of_nonadjacent_vertices P F.val.property G.val.property
    F.property.1 G.property.1 w.val z F.property.2
    (hc.squareCorners hdim w.val F).opposite_mem G.property.2 hzG hne hnadj
  exact Subtype.ext (Subtype.ext hfaces)

theorem squareCorners_cover_link_edge (hc : IsCubical P) (hdim : 3 ≤ P.dim)
    (v : VertexType P) (a b : NeighborOf v) (hab : (neighborLinkGraph v).Adj a b) :
    ∃ F : IncidentFaceType P v 2,
      ((hc.squareCorners hdim v F).left = a ∧ (hc.squareCorners hdim v F).right = b) ∨
      ((hc.squareCorners hdim v F).left = b ∧ (hc.squareCorners hdim v F).right = a) := by
  rcases hab with ⟨hne, F, hF, hdF, hv, ha, hb⟩
  let F' : IncidentFaceType P v 2 := ⟨⟨F, hF⟩, hdF, hv⟩
  let S := hc.squareCorners hdim v F'
  have ha' := S.all_neighbors a ha
  have hb' := S.all_neighbors b hb
  refine ⟨F', ?_⟩
  rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
  · exact False.elim (hne (ha'.trans hb'.symm))
  · exact Or.inl ⟨ha'.symm, hb'.symm⟩
  · exact Or.inr ⟨hb'.symm, ha'.symm⟩
  · exact False.elim (hne (ha'.trans hb'.symm))

abbrev FacetPins (f : FacetType P) (v : VertexType P) :=
  {a : NeighborOf v // a.val.val ∈ f.val.val}

def cubicalStarData (hc : IsCubical P) (hdim : 3 ≤ P.dim)
    (c : (polytopeGraph P).Coloring Bool) (f : FacetType P) (w : White c) :
    Cubical.StarData (black c) (white c) (NeighborOf w.val)
      (IncidentFaceType P w.val 2) (FacetPins f w.val) where
  center := w
  neighbor := coloredNeighbor c w
  centralEdge a := ⟨(coloredNeighbor c w a, w), a.property.symm⟩
  centralBlack _ := rfl
  centralWhite _ := rfl
  left F := (hc.squareCorners hdim w.val F).left
  right F := (hc.squareCorners hdim w.val F).right
  opposite := squareOpposite hc hdim c w
  leftEdge F := ⟨(coloredNeighbor c w (hc.squareCorners hdim w.val F).left,
    squareOpposite hc hdim c w F), (hc.squareCorners hdim w.val F).left_adj⟩
  rightEdge F := ⟨(coloredNeighbor c w (hc.squareCorners hdim w.val F).right,
    squareOpposite hc hdim c w F), (hc.squareCorners hdim w.val F).right_adj⟩
  leftBlack _ := rfl
  rightBlack _ := rfl
  leftWhite _ := rfl
  rightWhite _ := rfl
  pin := Subtype.val

def cubicalStarCover (hc : IsCubical P) (hdim : 3 ≤ P.dim)
    (c : (polytopeGraph P).Coloring Bool) :
    (cubicalFacetCover P hc hdim c).StarCover
      (fun j => NeighborOf j.val.2.val)
      (fun j => IncidentFaceType P j.val.2.val 2)
      (fun j => FacetPins j.val.1 j.val.2.val) where
  star j := cubicalStarData hc hdim c j.val.1 j.val.2
  center _ := rfl
  covers j e he := by
    have hwhite : white c e = j.val.2 := he
    have hAdj : (polytopeGraph P).Adj j.val.2.val (black c e).val := by
      rw [← hwhite]
      exact e.property.symm
    exact ⟨⟨(black c e).val, hAdj⟩, rfl⟩
  pinMem _ t := t.property
  link j := neighborLinkGraph j.val.2.val
  linkEdges j a b hab := squareCorners_cover_link_edge hc hdim j.val.2.val a b hab
  pin_injective _ := Subtype.val_injective
  opposite_injective j := squareOpposite_injective hc hdim c j.val.2
  opposite_ne_center j := squareOpposite_ne_center hc hdim c j.val.2

theorem IsCubical.facetPins_card (hc : IsCubical P) (hdim : 3 ≤ P.dim)
    (f : FacetType P) (v : VertexType P) (hv : v.val ∈ f.val.val) :
    Fintype.card (FacetPins f v) = P.dim - 1 := by
  let e : FacetPins f v ≃
      {a : VertexType P // a.val ∈ f.val.val ∧ (polytopeGraph P).Adj v a} := {
    toFun a := ⟨a.val.val, a.property, a.val.property⟩
    invFun a := ⟨⟨a.val, a.property.2⟩, a.property.1⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Fintype.card_congr e]
  have hdF := f.property
  exact (hc.face_neighbor_card P (by omega) f.val.property (by omega) v hv).trans (by omega)

end LeanEval.Geometry.PlatonicClassification
