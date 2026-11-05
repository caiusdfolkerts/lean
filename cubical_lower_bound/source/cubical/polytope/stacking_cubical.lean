import cubical.polytope.cube_enumerations

/-! # Genuine facet stackings preserve cubicality -/

open Set Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n m : ℕ} {P : ConvexPolytope n} {Q : ConvexPolytope m}

namespace FacetStacking

/-- The side facets are prisms on cubical ridges; all other facets are
retained or copied cubes. This derives cubicality from the gluing operation. -/
theorem isCubical (S : FacetStacking P Q) (hc : IsCubical P) (hdim : 3 ≤ P.dim) :
    IsCubical Q := by
  intro G hG hdG
  rw [S.dimension]
  let g : FaceType Q := ⟨G, hG⟩
  have hRank : (S.faceIso g).rank + 1 = P.dim := by
    rw [S.face_dimension, ← S.dimension]
    exact hdG
  have hne : S.faceIso g ≠ ⊤ := by
    intro h
    rw [h, StackingPoset.rank_top] at hRank
    omega
  let x : StackingCell P S.facet := (S.faceIso g).untop hne
  have hx : (x : StackingPoset P S.facet) = S.faceIso g := WithTop.coe_untop (S.faceIso g) hne
  have hxrank : x.rank + 1 = P.dim := by
    rw [← StackingPoset.rank_coe, hx]
    exact hRank
  have hback : S.faceIso.symm (x : StackingPoset P S.facet) = g := by
    rw [hx, S.faceIso.symm_apply_apply]
  have e := S.cellFaceOrderIso x
  rw [hback] at e
  obtain ⟨⟨H, l⟩, hvalid⟩ := x
  cases l with
  | lower =>
    change faceDim H.val < P.dim ∧ H ≠ S.facet.val at hvalid
    have hHd : faceDim H.val + 1 = P.dim := by simpa [StackingCell.rank] using hxrank
    obtain ⟨ψ⟩ := hc H.val H.property hHd
    exact ⟨e.trans ((StackingCell.lowerIntervalIso H hvalid).trans
      ((facePolytopeIntervalOrderIso P H).symm.trans ψ))⟩
  | upper =>
    change H ≤ S.facet.val at hvalid
    have hHd : faceDim H.val + 1 = P.dim := by simpa [StackingCell.rank] using hxrank
    obtain ⟨ψ⟩ := hc H.val H.property hHd
    exact ⟨e.trans ((StackingCell.upperIntervalIso H hvalid).trans
      ((facePolytopeIntervalOrderIso P H).symm.trans ψ))⟩
  | side =>
    change H < S.facet.val at hvalid
    have hHd : faceDim H.val + 2 = P.dim := by simpa [StackingCell.rank, Nat.add_assoc] using hxrank
    obtain ⟨ψ⟩ := hc.properFace_isCube P (by omega) H.property (by omega)
    let eb := (facePolytopeIntervalOrderIso P H).symm.trans ψ
    have et := e.trans ((StackingCell.sideIntervalIso H hvalid).trans
      ((prodOrderIso eb (OrderIso.refl StackingLayer)).trans
        (cubePrismFaceOrderIso (faceDim H.val) (by omega))))
    have heq : faceDim H.val + 1 = P.dim - 1 := by omega
    rw [heq] at et
    exact ⟨et⟩

end FacetStacking

/-- A stacked cubical polytope starts with a cube and is obtained by finite
facet gluings of the genuine ordinary face posets. The polytope at every
stage is an actual finite convex polytope. No face-number equalities or
cubical-preservation statements are part of the definition. -/
inductive IsStackedCubical : {n : ℕ} → ConvexPolytope n → Prop
  | cube {n d : ℕ} (P : ConvexPolytope n) (hd : 1 ≤ d)
      (h : CombinatoriallyEquivalent P (standardCube d)) : IsStackedCubical P
  | stack {n m : ℕ} {P : ConvexPolytope n} {Q : ConvexPolytope m}
      (hP : IsStackedCubical P) (S : FacetStacking P Q) : IsStackedCubical Q

theorem IsStackedCubical.standardCube (d : ℕ) (hd : 1 ≤ d) :
    IsStackedCubical (standardCube d) :=
  .cube _ hd ⟨OrderIso.refl _⟩

theorem IsStackedCubical.isCubical {P : ConvexPolytope n} (h : IsStackedCubical P) :
    3 ≤ P.dim → IsCubical P := by
  induction h with
  | cube P hd h =>
    intro _
    obtain ⟨φ⟩ := h
    exact (standardCube_isCubical _ hd).of_faceOrderIso φ.symm
  | stack hP S ih =>
    intro hd
    have hdP := S.dimension ▸ hd
    exact S.isCubical (ih hdP) hdP

end LeanEval.Geometry.PlatonicClassification
