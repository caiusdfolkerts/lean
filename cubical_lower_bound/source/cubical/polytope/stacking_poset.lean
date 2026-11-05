import cubical.polytope.facet_cover
import cubical.polytope.face_incidence
import Mathlib.Order.WithBot

/-!
# The ordinary face-poset operation of stacking a cube on a facet

The gluing keeps the old proper faces except the glued facet. It adds a
copy of every nonempty face of that facet, and a side prism over each of
its proper nonempty faces. Incidence is the product incidence of a prism,
with the bottom attached to the original boundary. A greatest element
then represents the whole new polytope.

No dimension, face count, or lower-bound assertion is included in the
stacking relation. Rank preservation is proved from the ordinary order.
-/

open Set Classical

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

inductive StackingLayer
  | lower | upper | side
  deriving DecidableEq

namespace StackingLayer

instance : Fintype StackingLayer where
  elems := {lower, upper, side}
  complete x := by cases x <;> simp

instance : PartialOrder StackingLayer where
  le a b := a = b ∨ b = side
  le_refl a := Or.inl rfl
  le_trans a b c hab hbc := by
    rcases hbc with rfl | rfl
    · exact hab
    · exact Or.inr rfl
  le_antisymm a b hab hba := by
    rcases hab with h | rfl
    · exact h
    · rcases hba with h | h
      · exact h.symm
      · exact h

@[simp] theorem le_iff (a b : StackingLayer) : a ≤ b ↔ a = b ∨ b = side := Iff.rfl

end StackingLayer

variable {n m : ℕ}

/-- The allowed nonempty boundary cells in a facet stacking. -/
def stackingCellValid (P : ConvexPolytope n) (F : FacetType P)
    (x : FaceType P × StackingLayer) : Prop :=
  match x.2 with
  | .lower => faceDim x.1.val < P.dim ∧ x.1 ≠ F.val
  | .upper => x.1 ≤ F.val
  | .side => x.1 < F.val

/-- The boundary face poset after gluing a prism over a chosen facet. -/
abbrev StackingCell (P : ConvexPolytope n) (F : FacetType P) :=
  {x : FaceType P × StackingLayer // stackingCellValid P F x}

instance stackingCellFintype (P : ConvexPolytope n) (F : FacetType P) :
    Fintype (StackingCell P F) := Fintype.ofFinite _

/-- The ordinary nonempty face poset of the glued boundary, with the whole
polytope adjoined as its greatest face. -/
abbrev StackingPoset (P : ConvexPolytope n) (F : FacetType P) :=
  WithTop (StackingCell P F)

def StackingCell.rank {P : ConvexPolytope n} {F : FacetType P}
    (x : StackingCell P F) : ℕ :=
  faceDim x.val.1.val + if x.val.2 = .side then 1 else 0

def StackingPoset.rank {P : ConvexPolytope n} {F : FacetType P}
    (x : StackingPoset P F) : ℕ :=
  WithTop.recTopCoe P.dim StackingCell.rank x

@[simp] theorem StackingPoset.rank_top (P : ConvexPolytope n) (F : FacetType P) :
    StackingPoset.rank (⊤ : StackingPoset P F) = P.dim := rfl

@[simp] theorem StackingPoset.rank_coe {P : ConvexPolytope n} {F : FacetType P}
    (x : StackingCell P F) : StackingPoset.rank (x : StackingPoset P F) = x.rank := rfl

theorem StackingCell.rank_lt_dim {P : ConvexPolytope n} {F : FacetType P}
    (x : StackingCell P F) : x.rank < P.dim := by
  obtain ⟨⟨G, l⟩, hx⟩ := x
  cases l with
  | lower => simpa [StackingCell.rank] using hx.1
  | upper =>
    have hle : faceDim G.val ≤ faceDim F.val.val :=
      Submodule.finrank_mono (vectorSpan_mono ℝ hx)
    have hF := F.property
    simp only [StackingCell.rank, reduceCtorEq, ↓reduceIte, Nat.add_zero]
    omega
  | side =>
    have hlt := faceDim_lt_of_ssubset P G.property F.val.property hx
    have hF := F.property
    simp only [StackingCell.rank, ↓reduceIte]
    omega

theorem StackingCell.rank_strictMono {P : ConvexPolytope n} {F : FacetType P} :
    StrictMono (StackingCell.rank (P := P) (F := F)) := by
  intro x y hxy
  have hle : x.val.1 ≤ y.val.1 := hxy.le.1
  have hdim : faceDim x.val.1.val ≤ faceDim y.val.1.val :=
    Submodule.finrank_mono (vectorSpan_mono ℝ hle)
  have htag : x.val.2 = y.val.2 ∨ y.val.2 = .side := hxy.le.2
  rcases htag with heq | hyside
  · have hne : x.val.1 ≠ y.val.1 := by
      intro heq'
      exact hxy.ne (Subtype.ext (Prod.ext heq' heq))
    have hlt := faceDim_lt_of_ssubset P x.val.1.property y.val.1.property
      (lt_of_le_of_ne hle (fun h => hne (Subtype.ext h)))
    simp only [StackingCell.rank, heq]
    omega
  · by_cases hxside : x.val.2 = .side
    · have heq : x.val.2 = y.val.2 := hxside.trans hyside.symm
      have hne : x.val.1 ≠ y.val.1 := by
        intro heq'
        exact hxy.ne (Subtype.ext (Prod.ext heq' heq))
      have hlt := faceDim_lt_of_ssubset P x.val.1.property y.val.1.property
        (lt_of_le_of_ne hle (fun h => hne (Subtype.ext h)))
      simp only [StackingCell.rank, hxside, hyside, ↓reduceIte]
      omega
    · simp only [StackingCell.rank, hxside, hyside, ↓reduceIte, Nat.add_zero]
      omega

theorem StackingPoset.rank_strictMono {P : ConvexPolytope n} {F : FacetType P} :
    StrictMono (StackingPoset.rank (P := P) (F := F)) := by
  intro x y hxy
  induction x using WithTop.recTopCoe with
  | top => exact (not_lt_of_ge le_top hxy).elim
  | coe x =>
    induction y using WithTop.recTopCoe with
    | top => exact x.rank_lt_dim
    | coe y => exact StackingCell.rank_strictMono (WithTop.coe_lt_coe.mp hxy)

/-- Every positive-dimensional geometric face has a codimension-one
nonempty subface, extracted from a complete flag. -/
theorem face_has_predecessor (P : ConvexPolytope n) (G : FaceType P)
    (hG : 0 < faceDim G.val) :
    ∃ H : FaceType P, H < G ∧ faceDim H.val + 1 = faceDim G.val := by
  obtain ⟨c, hc, hfaces, hmono⟩ := chain_ending_at_face P G.property rfl
  refine ⟨⟨c (faceDim G.val - 1), (hfaces _ (by omega)).1⟩, ?_, ?_⟩
  · change c (faceDim G.val - 1) ⊂ G.val
    simpa only [hc] using hmono (faceDim G.val - 1) (faceDim G.val) (by omega) le_rfl
  · rw [(hfaces _ (by omega)).2]
    omega

/-- Every positive rank in the gluing has a predecessor of rank one less. -/
theorem StackingCell.has_predecessor {P : ConvexPolytope n} {F : FacetType P}
    (x : StackingCell P F) (hx : 0 < x.rank) :
    ∃ y : StackingCell P F, y < x ∧ y.rank + 1 = x.rank := by
  obtain ⟨⟨G, l⟩, hvalid⟩ := x
  cases l with
  | lower =>
    change faceDim G.val < P.dim ∧ G ≠ F.val at hvalid
    have hpos : 0 < faceDim G.val := by simpa [StackingCell.rank] using hx
    obtain ⟨H, hHG, hdim⟩ := face_has_predecessor P G hpos
    have hHd : faceDim H.val < P.dim := by
      have := hvalid.1
      omega
    have hHF : H ≠ F.val := by
      intro h
      have hF := F.property
      rw [h] at hdim
      have := hvalid.1
      omega
    refine ⟨⟨(H, .lower), hHd, hHF⟩, ?_, ?_⟩
    · exact lt_of_le_of_ne ⟨hHG.le, le_rfl⟩ (fun h => hHG.ne (congrArg (fun z => z.val.1) h))
    · simpa [StackingCell.rank] using hdim
  | upper =>
    change G ≤ F.val at hvalid
    have hpos : 0 < faceDim G.val := by simpa [StackingCell.rank] using hx
    obtain ⟨H, hHG, hdim⟩ := face_has_predecessor P G hpos
    refine ⟨⟨(H, .upper), hHG.le.trans hvalid⟩, ?_, ?_⟩
    · exact lt_of_le_of_ne ⟨hHG.le, le_rfl⟩ (fun h => hHG.ne (congrArg (fun z => z.val.1) h))
    · simpa [StackingCell.rank] using hdim
  | side =>
    change G < F.val at hvalid
    have hdim := faceDim_lt_of_ssubset P G.property F.val.property hvalid
    have hF := F.property
    refine ⟨⟨(G, .lower), (show faceDim G.val < P.dim from by omega), ne_of_lt hvalid⟩, ?_, ?_⟩
    · refine lt_of_le_of_ne ⟨le_rfl, Or.inr rfl⟩ ?_
      intro h
      have := congrArg (fun z => z.val.2) h
      contradiction
    · simp [StackingCell.rank]

theorem StackingPoset.has_predecessor {P : ConvexPolytope n} {F : FacetType P}
    (x : StackingPoset P F) (hx : 0 < x.rank) :
    ∃ y : StackingPoset P F, y < x ∧ y.rank + 1 = x.rank := by
  induction x using WithTop.recTopCoe with
  | top =>
    let y : StackingCell P F := ⟨(F.val, .upper), le_rfl⟩
    refine ⟨y, WithTop.coe_lt_top y, ?_⟩
    simpa [y, StackingCell.rank] using F.property
  | coe x =>
    obtain ⟨y, hy, hr⟩ := x.has_predecessor hx
    exact ⟨y, WithTop.coe_lt_coe.mpr hy, hr⟩

/-- A genuine facet stacking is an isomorphism of the ordinary nonempty
face posets to the gluing poset. No numerical conclusion is assumed. -/
structure FacetStacking (P : ConvexPolytope n) (Q : ConvexPolytope m) where
  facet : FacetType P
  faceIso : FaceType Q ≃o StackingPoset P facet

namespace FacetStacking

variable {P : ConvexPolytope n} {Q : ConvexPolytope m} (S : FacetStacking P Q)

/-- Rank in the glued face poset equals the actual affine dimension in Q. -/
theorem face_dimension (G : FaceType Q) : (S.faceIso G).rank = faceDim G.val := by
  have hupper : faceDim G.val ≤ (S.faceIso G).rank := by
    let d := faceDim G.val
    obtain ⟨c, hcd, hcface, hcmono⟩ := chain_ending_at_face Q G.property (d := d) rfl
    let C (k : ℕ) : FaceType Q := if hk : k ≤ d then ⟨c k, (hcface k hk).1⟩ else G
    have hC (k : ℕ) (hk : k ≤ d) : (C k).val = c k := by simp only [C, dif_pos hk]
    have hCd : C d = G := Subtype.ext ((hC d le_rfl).trans hcd)
    have hstrict : StrictMonoOn (fun k => (S.faceIso (C k)).rank) (Iic d) := by
      intro i hi j hj hij
      apply StackingPoset.rank_strictMono
      apply S.faceIso.strictMono
      change (C i).val ⊂ (C j).val
      rw [hC i hi, hC j hj]
      exact hcmono i j hij hj
    have hbound := hstrict.Iic_id_le d le_rfl
    simpa only [hCd, d] using hbound
  have hlower : ∀ r : ℕ, ∀ x : StackingPoset P S.facet, x.rank = r →
      x.rank ≤ faceDim (S.faceIso.symm x).val := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro x hr
      by_cases hz : x.rank = 0
      · simp only [hz, Nat.zero_le]
      · obtain ⟨y, hyx, hyr⟩ := x.has_predecessor (by omega)
        have hiy := ih y.rank (by omega) y rfl
        have hdim := faceDim_lt_of_ssubset Q (S.faceIso.symm y).property
          (S.faceIso.symm x).property (S.faceIso.symm.strictMono hyx)
        omega
  have h := hlower (S.faceIso G).rank (S.faceIso G) rfl
  simp only [S.faceIso.symm_apply_apply] at h
  exact le_antisymm h hupper

include S in
/-- Stacking preserves intrinsic dimension, as a consequence of the face order. -/
theorem dimension : Q.dim = P.dim := by
  let T : FaceType Q := ⟨Q.toSet, toSet_isFace Q⟩
  have htop : S.faceIso T = ⊤ := by
    apply top_le_iff.mp
    rw [← S.faceIso.apply_symm_apply ⊤]
    apply S.faceIso.monotone
    exact face_subset_toSet Q (S.faceIso.symm ⊤).property
  have h := S.face_dimension T
  rw [htop, StackingPoset.rank_top] at h
  exact h.symm

end FacetStacking

end LeanEval.Geometry.PlatonicClassification
