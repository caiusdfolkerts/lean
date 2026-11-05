module
public import FinitePolygonTemplates
public import RawCellSemantics
public import FiniteChecks

@[expose] public section

/-!
# Complete numerical profiles of the seven-vertex facet catalogue

The index is the canonical polygon-template index. It agrees with the original
34-model seven-vertex catalogue, without applying the legacy six-type permutation.
The following small certificates recompute every profile from the complete
polygon and edge data; the literal table is not an assumed classification.
-/

namespace Papers.RationalityTen.SevenFacetTemplateProfiles
open Finset
open MatroidChecked.FacetBoundaryEncoding ActualFacetCatalogueTransport
open PolygonBoundaryCatalogue FiniteCycleCandidates CellFacetInvariants

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def quadrilateralVertices {n : Nat} (C : Cell n) : Finset (Fin n) :=
  (C.ridges.filter fun S => S.card = 4).biUnion id

structure Profile where
  triangles : Nat
  quadrilaterals : Nat
  pentagons : Nat
  hexagons : Nat
  faces : Nat
  quadrilateralVertices : Nat
  deriving DecidableEq

def polygonProfile {n : Nat} (B : Finset (Polygon n)) : Profile where
  triangles := (B.filter fun R => R.vertices.card = 3).card
  quadrilaterals := (B.filter fun R => R.vertices.card = 4).card
  pentagons := (B.filter fun R => R.vertices.card = 5).card
  hexagons := (B.filter fun R => R.vertices.card = 6).card
  faces := B.card
  quadrilateralVertices := ((B.filter fun R => R.vertices.card = 4).biUnion
    fun R => R.vertices).card

def cellProfile {n : Nat} (C : Cell n) : Profile where
  triangles := cellRidgeSizeCount C 3
  quadrilaterals := cellRidgeSizeCount C 4
  pentagons := cellRidgeSizeCount C 5
  hexagons := cellRidgeSizeCount C 6
  faces := C.ridges.card
  quadrilateralVertices := (quadrilateralVertices C).card

/-- All thirty-four profiles, in canonical order. -/
def literal (i : Fin 34) : Profile :=
  match i.val with
  | 0 => ⟨10, 0, 0, 0, 10, 0⟩
  | 1 => ⟨10, 0, 0, 0, 10, 0⟩
  | 2 => ⟨8, 1, 0, 0, 9, 4⟩
  | 3 => ⟨8, 1, 0, 0, 9, 4⟩
  | 4 => ⟨10, 0, 0, 0, 10, 0⟩
  | 5 => ⟨10, 0, 0, 0, 10, 0⟩
  | 6 => ⟨8, 1, 0, 0, 9, 4⟩
  | 7 => ⟨8, 1, 0, 0, 9, 4⟩
  | 8 => ⟨8, 1, 0, 0, 9, 4⟩
  | 9 => ⟨8, 1, 0, 0, 9, 4⟩
  | 10 => ⟨7, 0, 1, 0, 8, 0⟩
  | 11 => ⟨6, 2, 0, 0, 8, 6⟩
  | 12 => ⟨6, 2, 0, 0, 8, 6⟩
  | 13 => ⟨4, 3, 0, 0, 7, 6⟩
  | 14 => ⟨10, 0, 0, 0, 10, 0⟩
  | 15 => ⟨8, 1, 0, 0, 9, 4⟩
  | 16 => ⟨8, 1, 0, 0, 9, 4⟩
  | 17 => ⟨7, 0, 1, 0, 8, 0⟩
  | 18 => ⟨6, 2, 0, 0, 8, 6⟩
  | 19 => ⟨6, 2, 0, 0, 8, 6⟩
  | 20 => ⟨6, 2, 0, 0, 8, 6⟩
  | 21 => ⟨6, 2, 0, 0, 8, 6⟩
  | 22 => ⟨6, 0, 0, 1, 7, 0⟩
  | 23 => ⟨6, 2, 0, 0, 8, 7⟩
  | 24 => ⟨6, 2, 0, 0, 8, 7⟩
  | 25 => ⟨4, 3, 0, 0, 7, 7⟩
  | 26 => ⟨5, 1, 1, 0, 7, 4⟩
  | 27 => ⟨4, 3, 0, 0, 7, 7⟩
  | 28 => ⟨6, 2, 0, 0, 8, 7⟩
  | 29 => ⟨4, 3, 0, 0, 7, 7⟩
  | 30 => ⟨5, 1, 1, 0, 7, 4⟩
  | 31 => ⟨4, 3, 0, 0, 7, 7⟩
  | 32 => ⟨3, 2, 1, 0, 6, 6⟩
  | _ => ⟨2, 4, 0, 0, 6, 7⟩

def profileCheck (i : Fin 34) : Bool := decide
  (polygonProfile (N7.templates i) = literal i ∧
    cellProfile (cellOfBoundary (N7.templates i)) = literal i)

private theorem profile_0_4 : FiniteChecks.Interval
    (fun i => profileCheck (Fin.ofNat 34 i)) 0 4 := by
  exact FiniteChecks.interval_of_check _ 0 4 (by decide +kernel)

private theorem profile_4_8 : FiniteChecks.Interval
    (fun i => profileCheck (Fin.ofNat 34 i)) 4 8 := by
  exact FiniteChecks.interval_of_check _ 4 4 (by decide +kernel)

private theorem profile_8_12 : FiniteChecks.Interval
    (fun i => profileCheck (Fin.ofNat 34 i)) 8 12 := by
  exact FiniteChecks.interval_of_check _ 8 4 (by decide +kernel)

private theorem profile_12_16 : FiniteChecks.Interval
    (fun i => profileCheck (Fin.ofNat 34 i)) 12 16 := by
  exact FiniteChecks.interval_of_check _ 12 4 (by decide +kernel)

private theorem profile_16_20 : FiniteChecks.Interval
    (fun i => profileCheck (Fin.ofNat 34 i)) 16 20 := by
  exact FiniteChecks.interval_of_check _ 16 4 (by decide +kernel)

private theorem profile_20_24 : FiniteChecks.Interval
    (fun i => profileCheck (Fin.ofNat 34 i)) 20 24 := by
  exact FiniteChecks.interval_of_check _ 20 4 (by decide +kernel)

private theorem profile_24_28 : FiniteChecks.Interval
    (fun i => profileCheck (Fin.ofNat 34 i)) 24 28 := by
  exact FiniteChecks.interval_of_check _ 24 4 (by decide +kernel)

private theorem profile_28_32 : FiniteChecks.Interval
    (fun i => profileCheck (Fin.ofNat 34 i)) 28 32 := by
  exact FiniteChecks.interval_of_check _ 28 4 (by decide +kernel)

private theorem profile_32_34 : FiniteChecks.Interval
    (fun i => profileCheck (Fin.ofNat 34 i)) 32 34 := by
  exact FiniteChecks.interval_of_check _ 32 2 (by decide +kernel)

private theorem joined_0_8 : FiniteChecks.Interval
    (fun i => profileCheck (Fin.ofNat 34 i)) 0 8 :=
  FiniteChecks.interval_append _ 0 4 8 profile_0_4 profile_4_8

private theorem joined_8_16 : FiniteChecks.Interval
    (fun i => profileCheck (Fin.ofNat 34 i)) 8 16 :=
  FiniteChecks.interval_append _ 8 12 16 profile_8_12 profile_12_16

private theorem joined_16_24 : FiniteChecks.Interval
    (fun i => profileCheck (Fin.ofNat 34 i)) 16 24 :=
  FiniteChecks.interval_append _ 16 20 24 profile_16_20 profile_20_24

private theorem joined_24_32 : FiniteChecks.Interval
    (fun i => profileCheck (Fin.ofNat 34 i)) 24 32 :=
  FiniteChecks.interval_append _ 24 28 32 profile_24_28 profile_28_32

private theorem joined_0_16 : FiniteChecks.Interval
    (fun i => profileCheck (Fin.ofNat 34 i)) 0 16 :=
  FiniteChecks.interval_append _ 0 8 16 joined_0_8 joined_8_16

private theorem joined_16_32 : FiniteChecks.Interval
    (fun i => profileCheck (Fin.ofNat 34 i)) 16 32 :=
  FiniteChecks.interval_append _ 16 24 32 joined_16_24 joined_24_32

private theorem joined_0_32 : FiniteChecks.Interval
    (fun i => profileCheck (Fin.ofNat 34 i)) 0 32 :=
  FiniteChecks.interval_append _ 0 16 32 joined_0_16 joined_16_32

private theorem joined_0_34 : FiniteChecks.Interval
    (fun i => profileCheck (Fin.ofNat 34 i)) 0 34 :=
  FiniteChecks.interval_append _ 0 32 34 joined_0_32 profile_32_34

/-- Both the polygon and decoded-cell views have exactly the displayed data. -/
theorem profile_exact (i : Fin 34) :
    polygonProfile (N7.templates i) = literal i ∧
      cellProfile (cellOfBoundary (N7.templates i)) = literal i :=
  of_decide_eq_true (FiniteChecks.fin_of_interval profileCheck joined_0_34 i)

/-- Three quadrilaterals using only six vertices uniquely identify the capped
prism, index 13. No extra hypothesis about polygon sizes is used here. -/
theorem signature_identifies : ∀ i : Fin 34,
    (literal i).quadrilaterals = 3 →
    (literal i).quadrilateralVertices = 6 → i = 13 := by
  decide +kernel

theorem cell_signature_identifies (i : Fin 34)
    (hq : cellRidgeSizeCount (cellOfBoundary (N7.templates i)) 4 = 3)
    (hu : (quadrilateralVertices (cellOfBoundary (N7.templates i))).card = 6) :
    i = 13 := by
  have hp := (profile_exact i).2
  have hq' := congrArg Profile.quadrilaterals hp
  have hu' := congrArg Profile.quadrilateralVertices hp
  exact signature_identifies i (hq'.symm.trans hq) (hu'.symm.trans hu)

/-- Only canonical six-type 6 (the triangular prism) can have polygon excess
three. The pentagonal pyramid is canonical type 4. -/
theorem six_excess_bound : ∀ i : Fin 7,
    cellExcess (cellOfBoundary (N6.templates i)) ≤ (if i = 6 then 3 else 2) := by
  decide +kernel

end Papers.RationalityTen.SevenFacetTemplateProfiles
