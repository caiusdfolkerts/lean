import cubical.polytope.stacking_counts

/-! # Face intervals in a genuine facet stacking -/

open Set Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n m : ℕ}

/-- Adjoining a greatest element does not change the lower interval of
any original element. -/
def withTopIicOrderIso {α : Type*} [PartialOrder α] (x : α) :
    {y : α // y ≤ x} ≃o {y : WithTop α // y ≤ (x : WithTop α)} := by
  let f : {y : α // y ≤ x} → {y : WithTop α // y ≤ (x : WithTop α)} :=
    fun y => ⟨y.val, WithTop.coe_le_coe.mpr y.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro y z h
      apply Subtype.ext
      exact WithTop.coe_injective (congrArg Subtype.val h)
    · rintro ⟨y, hy⟩
      induction y using WithTop.recTopCoe with
      | top => exact (WithTop.not_top_le_coe x hy).elim
      | coe y => exact ⟨⟨y, WithTop.coe_le_coe.mp hy⟩, rfl⟩
  exact {
    __ := Equiv.ofBijective f hf
    map_rel_iff' := by intro y z; exact WithTop.coe_le_coe }

theorem old_cell_valid_of_le {P : ConvexPolytope n} {F : FacetType P}
    {G H : FaceType P} (hG : faceDim G.val < P.dim ∧ G ≠ F.val) (hHG : H ≤ G) :
    faceDim H.val < P.dim ∧ H ≠ F.val := by
  have hdim : faceDim H.val ≤ faceDim G.val :=
    Submodule.finrank_mono (vectorSpan_mono ℝ hHG)
  refine ⟨hdim.trans_lt hG.1, ?_⟩
  intro heq
  have hFG : F.val < G := lt_of_le_of_ne (heq ▸ hHG) hG.2.symm
  have hlt := faceDim_lt_of_ssubset P F.val.property G.property hFG
  have hF := F.property
  omega

namespace StackingCell

variable {P : ConvexPolytope n} {F : FacetType P}

def lowerCell (G : FaceType P) (hG : faceDim G.val < P.dim ∧ G ≠ F.val) :
    StackingCell P F := ⟨(G, .lower), hG⟩

def upperCell (G : FaceType P) (hG : G ≤ F.val) : StackingCell P F :=
  ⟨(G, .upper), hG⟩

def sideCell (G : FaceType P) (hG : G < F.val) : StackingCell P F :=
  ⟨(G, .side), hG⟩

theorem layer_eq_lower_of_le_lower {G : FaceType P}
    {hG : faceDim G.val < P.dim ∧ G ≠ F.val}
    (y : {y : StackingCell P F // y ≤ lowerCell G hG}) : y.val.val.2 = .lower := by
  have h := y.property.2
  change y.val.val.2 = .lower ∨ StackingLayer.lower = .side at h
  simpa using h

theorem layer_eq_upper_of_le_upper {G : FaceType P} {hG : G ≤ F.val}
    (y : {y : StackingCell P F // y ≤ upperCell G hG}) : y.val.val.2 = .upper := by
  have h := y.property.2
  change y.val.val.2 = .upper ∨ StackingLayer.upper = .side at h
  simpa using h

/-- Every retained old face retains its entire face interval. -/
def lowerIntervalIso (G : FaceType P) (hG : faceDim G.val < P.dim ∧ G ≠ F.val) :
    {y : StackingCell P F // y ≤ lowerCell G hG} ≃o {H : FaceType P // H ≤ G} where
  toFun y := ⟨y.val.val.1, y.property.1⟩
  invFun H := ⟨lowerCell H.val (old_cell_valid_of_le hG H.property), ⟨H.property, le_rfl⟩⟩
  left_inv y := Subtype.ext (Subtype.ext (Prod.ext rfl (layer_eq_lower_of_le_lower y).symm))
  right_inv _ := rfl
  map_rel_iff' := by
    intro y z
    constructor
    · intro h
      exact ⟨h, by
        rw [layer_eq_lower_of_le_lower y, layer_eq_lower_of_le_lower z]⟩
    · exact fun h => h.1

/-- A copied top face has the ordinary face interval of its original. -/
def upperIntervalIso (G : FaceType P) (hG : G ≤ F.val) :
    {y : StackingCell P F // y ≤ upperCell G hG} ≃o {H : FaceType P // H ≤ G} where
  toFun y := ⟨y.val.val.1, y.property.1⟩
  invFun H := ⟨upperCell H.val (H.property.trans hG), ⟨H.property, le_rfl⟩⟩
  left_inv y := Subtype.ext (Subtype.ext (Prod.ext rfl (layer_eq_upper_of_le_upper y).symm))
  right_inv _ := rfl
  map_rel_iff' := by
    intro y z
    constructor
    · intro h
      exact ⟨h, by
        rw [layer_eq_upper_of_le_upper y, layer_eq_upper_of_le_upper z]⟩
    · exact fun h => h.1

/-- The face interval of a side prism is the product of the base face
interval with the three-element face poset of an interval. -/
def sideIntervalIso (G : FaceType P) (hG : G < F.val) :
    {y : StackingCell P F // y ≤ sideCell G hG} ≃o
      {H : FaceType P // H ≤ G} × StackingLayer where
  toFun y := (⟨y.val.val.1, y.property.1⟩, y.val.val.2)
  invFun H := by
    have hHF : H.1.val < F.val := H.1.property.trans_lt hG
    have hvalid : stackingCellValid P F (H.1.val, H.2) := by
      cases H.2 with
      | lower =>
        have hdim := faceDim_lt_of_ssubset P H.1.val.property F.val.property hHF
        have hF := F.property
        exact ⟨by change faceDim H.1.val.val < P.dim; omega, ne_of_lt hHF⟩
      | upper => exact hHF.le
      | side => exact hHF
    exact ⟨⟨(H.1.val, H.2), hvalid⟩, ⟨H.1.property, Or.inr rfl⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

end StackingCell

namespace FacetStacking

variable {P : ConvexPolytope n} {Q : ConvexPolytope m} (S : FacetStacking P Q)

/-- Actual geometric faces of the new polytope have precisely the lower
intervals prescribed by the gluing poset. -/
def cellFaceOrderIso (x : StackingCell P S.facet) :
    FaceType (facePolytope Q (S.faceIso.symm (x : StackingPoset P S.facet)).property) ≃o
      {y : StackingCell P S.facet // y ≤ x} := by
  let e : {G : FaceType Q // G ≤ S.faceIso.symm (x : StackingPoset P S.facet)} ≃o
      {y : StackingPoset P S.facet // y ≤ (x : StackingPoset P S.facet)} := {
    toFun G := ⟨S.faceIso G.val, by
      simpa only [S.faceIso.apply_symm_apply] using S.faceIso.monotone G.property⟩
    invFun y := ⟨S.faceIso.symm y.val, S.faceIso.symm.monotone y.property⟩
    left_inv G := Subtype.ext (S.faceIso.symm_apply_apply G.val)
    right_inv y := Subtype.ext (S.faceIso.apply_symm_apply y.val)
    map_rel_iff' := S.faceIso.map_rel_iff }
  exact (facePolytopeIntervalOrderIso Q (S.faceIso.symm (x : StackingPoset P S.facet))).trans
    (e.trans (withTopIicOrderIso x).symm)

end FacetStacking

end LeanEval.Geometry.PlatonicClassification
