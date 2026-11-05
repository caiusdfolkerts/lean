import cubical.polytope.stacking_poset

/-! # Face counts derived from the facet-gluing poset -/

open Set Classical
open scoped BigOperators

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n m : ℕ}

/-- Faces of a face-polytope are exactly the lower interval of that face
in the original ordinary face poset. -/
def facePolytopeIntervalOrderIso (P : ConvexPolytope n) (F : FaceType P) :
    FaceType (facePolytope P F.property) ≃o {G : FaceType P // G ≤ F} where
  toFun G := ⟨⟨G.val, isFace_of_facePolytope P F.property G.property⟩, by
    change G.val ⊆ F.val
    have h := face_subset_toSet (facePolytope P F.property) G.property
    simpa only [facePolytope_toSet] using h⟩
  invFun G := ⟨G.val.val, facePolytope_isFace_of P F.property G.val.property G.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem card_faces_below (P : ConvexPolytope n) (F : FaceType P) (i : ℕ) :
    Fintype.card {G : FaceType P // faceDim G.val = i ∧ G ≤ F} =
      faceNumber (facePolytope P F.property) i := by
  let e : {G : FaceType P // faceDim G.val = i ∧ G ≤ F} ≃
      DimFaceType (facePolytope P F.property) i := {
    toFun G := ⟨⟨G.val.val, facePolytope_isFace_of P F.property G.val.property G.property.2⟩,
      G.property.1⟩
    invFun G := ⟨⟨G.val.val, isFace_of_facePolytope P F.property G.val.property⟩,
      G.property, by
        change G.val.val ⊆ F.val
        have h := face_subset_toSet (facePolytope P F.property) G.val.property
        simpa only [facePolytope_toSet] using h⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact (Fintype.card_congr e).trans (card_dimFaceType _ _)

theorem StackingCell.rank_card (P : ConvexPolytope n) (F : FacetType P) (i : ℕ) :
    Fintype.card {x : StackingCell P F // x.rank = i} =
      Fintype.card {G : FaceType P // faceDim G.val = i ∧ faceDim G.val < P.dim ∧ G ≠ F.val} +
      Fintype.card {G : FaceType P // faceDim G.val = i ∧ G ≤ F.val} +
      Fintype.card {G : FaceType P // faceDim G.val + 1 = i ∧ G < F.val} := by
  let T (l : StackingLayer) := {G : FaceType P //
    stackingCellValid P F (G, l) ∧ faceDim G.val + (if l = .side then 1 else 0) = i}
  let e : {x : StackingCell P F // x.rank = i} ≃ Σ l : StackingLayer, T l := {
    toFun x := ⟨x.val.val.2, ⟨x.val.val.1, x.val.property, x.property⟩⟩
    invFun x := ⟨⟨(x.2.val, x.1), x.2.property.1⟩, x.2.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  have hsum : (∑ l : StackingLayer, Fintype.card (T l)) =
      Fintype.card (T .lower) + Fintype.card (T .upper) + Fintype.card (T .side) := by
    change (∑ l ∈ ({.lower, .upper, .side} : Finset StackingLayer), Fintype.card (T l)) = _
    simp [Nat.add_assoc]
  rw [hsum]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  all_goals
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro G
    simp [T, stackingCellValid, and_comm, and_left_comm, and_assoc]

namespace FacetStacking

variable {P : ConvexPolytope n} {Q : ConvexPolytope m} (S : FacetStacking P Q)

theorem faceNumber_eq_rank_card (i : ℕ) (hi : i < P.dim) :
    faceNumber Q i = Fintype.card {x : StackingCell P S.facet // x.rank = i} := by
  letI : Fintype (StackingPoset P S.facet) :=
    Fintype.ofEquiv (FaceType Q) S.faceIso.toEquiv
  let e := S.faceIso.toEquiv.subtypeEquiv (p := fun G => faceDim G.val = i)
    (q := fun x => x.rank = i) (fun G => by
      change faceDim G.val = i ↔ (S.faceIso G).rank = i
      rw [S.face_dimension])
  let f : {x : StackingCell P S.facet // x.rank = i} →
      {x : StackingPoset P S.facet // x.rank = i} := fun x => ⟨x.val, x.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      exact WithTop.coe_injective (congrArg Subtype.val h)
    · rintro ⟨x, hx⟩
      induction x using WithTop.recTopCoe with
      | top => simp only [StackingPoset.rank_top] at hx; omega
      | coe x => exact ⟨⟨x, hx⟩, rfl⟩
  calc
    faceNumber Q i = Fintype.card (DimFaceType Q i) := (card_dimFaceType _ _).symm
    _ = Fintype.card {x : StackingPoset P S.facet // x.rank = i} := Fintype.card_congr e
    _ = Fintype.card {x : StackingCell P S.facet // x.rank = i} :=
      (Fintype.card_congr (Equiv.ofBijective f hf)).symm

theorem old_rank_card (i : ℕ) (hi : i < P.dim) (hne : i + 1 ≠ P.dim) :
    Fintype.card {G : FaceType P // faceDim G.val = i ∧ faceDim G.val < P.dim ∧ G ≠ S.facet.val} =
      faceNumber P i := by
  rw [← card_dimFaceType]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro G
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, h ▸ hi, ?_⟩
    intro heq
    have hf := S.facet.property
    rw [← heq, h] at hf
    exact hne hf

theorem old_facet_rank_card (hdim : 1 ≤ P.dim) :
    Fintype.card {G : FaceType P // faceDim G.val = P.dim - 1 ∧
      faceDim G.val < P.dim ∧ G ≠ S.facet.val} + 1 = faceNumber P (P.dim - 1) := by
  let F : DimFaceType P (P.dim - 1) := ⟨S.facet.val, by have := S.facet.property; omega⟩
  let e : {G : FaceType P // faceDim G.val = P.dim - 1 ∧
        faceDim G.val < P.dim ∧ G ≠ S.facet.val} ≃
      {G : DimFaceType P (P.dim - 1) // G ≠ F} := {
    toFun G := ⟨⟨G.val, G.property.1⟩, fun h => G.property.2.2 (congrArg Subtype.val h)⟩
    invFun G := ⟨G.val.val, G.val.property, by rw [G.val.property]; omega,
      fun h => G.property (Subtype.ext h)⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Fintype.card_congr e, ← card_dimFaceType]
  have h := Fintype.card_subtype_compl (fun G : DimFaceType P (P.dim - 1) => G = F)
  simp only [Fintype.card_subtype_eq] at h
  rw [h]
  have hpos : 0 < Fintype.card (DimFaceType P (P.dim - 1)) :=
    Fintype.card_pos_iff.mpr ⟨F⟩
  omega

theorem side_rank_card (i : ℕ) (hi : 1 ≤ i) (hid : i < P.dim) :
    Fintype.card {G : FaceType P // faceDim G.val + 1 = i ∧ G < S.facet.val} =
      faceNumber (facePolytope P S.facet.val.property) (i - 1) := by
  rw [← card_faces_below P S.facet.val (i - 1)]
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro G
  constructor
  · rintro ⟨h, hlt⟩
    exact ⟨by omega, hlt.le⟩
  · rintro ⟨h, hle⟩
    refine ⟨by omega, lt_of_le_of_ne hle ?_⟩
    intro heq
    have hf := S.facet.property
    rw [← heq, h] at hf
    omega

/-- All positive proper-face counts follow from the three disjoint layers
of the gluing poset. -/
theorem faceNumber_positive (i : ℕ) (hi : 1 ≤ i) (hid : i + 1 < P.dim) :
    faceNumber Q i = faceNumber P i +
      faceNumber (facePolytope P S.facet.val.property) i +
      faceNumber (facePolytope P S.facet.val.property) (i - 1) := by
  rw [S.faceNumber_eq_rank_card i (by omega), StackingCell.rank_card,
    S.old_rank_card i (by omega) (by omega), card_faces_below,
    S.side_rank_card i hi (by omega)]

/-- A stacking adds one new copy of the glued facet's vertices. -/
theorem vertices_card (hdim : 2 ≤ P.dim) :
    Q.vertices.card = P.vertices.card + (facePolytope P S.facet.val.property).vertices.card := by
  have hz : Fintype.card {G : FaceType P // faceDim G.val + 1 = 0 ∧ G < S.facet.val} = 0 := by
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun G => by have := G.property.1; omega⟩
  rw [← faceNumber_zero, S.faceNumber_eq_rank_card 0 (by omega), StackingCell.rank_card,
    S.old_rank_card 0 (by omega) (by omega), card_faces_below, hz, Nat.add_zero,
    faceNumber_zero, faceNumber_zero]

/-- The facet count balances removal of the glued facet against the new
top facet and its side prisms. -/
theorem facet_count_balance (hdim : 2 ≤ P.dim) :
    faceNumber Q (P.dim - 1) + 1 = faceNumber P (P.dim - 1) +
      faceNumber (facePolytope P S.facet.val.property) (P.dim - 1) +
      faceNumber (facePolytope P S.facet.val.property) (P.dim - 2) := by
  rw [S.faceNumber_eq_rank_card (P.dim - 1) (by omega), StackingCell.rank_card,
    card_faces_below, S.side_rank_card (P.dim - 1) (by omega) (by omega)]
  have hs : P.dim - 1 - 1 = P.dim - 2 := by omega
  rw [hs]
  have h := S.old_facet_rank_card (by omega)
  omega

end FacetStacking

end LeanEval.Geometry.PlatonicClassification
