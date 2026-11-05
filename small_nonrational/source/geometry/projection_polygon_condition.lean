module
public import TerminalGeometry
public import PaperPolygon.RawBounds
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Finset.Card

@[expose] public section

/-!
# The explicit polygon-size hypothesis in Proposition 7

The paper requires that each polygon avoiding the chosen projection vertex
have at most four vertices. A reconstruction certificate alone does not
record this extra hypothesis. The structure below records both, with the
projection centre represented by label zero after relabelling.
-/

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection

def AllPolygonsSmall {n : Nat} (B : Boundary n) : Prop :=
  ∀ R ∈ B.polygons, R.card ≤ 4

def ProjectionPolygonBound {n : Nat} (B : Boundary n) : Prop :=
  ∀ R ∈ B.polygons, 0 ∉ R → R.card ≤ 4

structure PaperCertifiedRelabelling {n : Nat} (B : Boundary n)
    extends CertifiedRelabelling B where
  polygons_avoiding_center : ProjectionPolygonBound target

theorem AllPolygonsSmall.relabel {n : Nat} {B : Boundary n}
    (hB : AllPolygonsSmall B) (σ : Fin (n + 1) ≃ Fin (n + 1)) :
    AllPolygonsSmall (B.relabel σ) := by
  intro R hR
  change R ∈ B.polygons.image (fun S => S.image σ) at hR
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hR
  rw [Finset.card_image_of_injective _ σ.injective]
  exact hB S hS

def CertifiedRelabelling.with_small_polygons {n : Nat} {B : Boundary n}
    (C : CertifiedRelabelling B) (hB : AllPolygonsSmall B) :
    PaperCertifiedRelabelling B where
  toCertifiedRelabelling := C
  polygons_avoiding_center := by
    have htarget := hB.relabel C.permutation
    rw [C.boundary_eq] at htarget
    intro R hR _
    exact htarget R hR

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection

namespace Nonrational.TerminalVerification

open Nonrational.TerminalData
open Papers.RationalityTen.ChirotopeDensity.FiniteProjection

def PaperCertifies (j : Nat) : Prop :=
  Nonempty (PaperCertifiedRelabelling (decode (targets j)))

theorem decodeMask_card (m : Nat) : (decodeMask m).card = PaperPolygon.maskCard m := by
  have heq : decodeMask m =
      ((List.finRange 10).filter fun i => m.testBit i.val).toFinset := by
    ext i
    simp [decodeMask, List.mem_finRange]
  rw [heq, List.toFinset_card_of_nodup
    (List.Nodup.filter _ (List.nodup_finRange 10))]
  rfl

theorem allPolygonsSmall_of_raw_check {j : Nat}
    (hcheck : PaperPolygon.targetCheck j = true) (hj : j ≠ 1982) :
    AllPolygonsSmall (decode (targets j)) := by
  intro R hR
  change R ∈ (targets j).polygons.toFinset.image decodeMask at hR
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hR
  rw [decodeMask_card]
  exact PaperPolygon.targetCheck_sound hcheck hj m (List.mem_toFinset.mp hm)

end Nonrational.TerminalVerification
