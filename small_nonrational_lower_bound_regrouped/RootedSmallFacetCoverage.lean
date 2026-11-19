module

public import RootedCellLookupSemantics
public import FullSmallFacetActualCoverage

@[expose] public section

/-!
# Every eligible actual small facet belongs to a checked rooted universe

The source universe is the complete6510-cell table. Positive quota kinds
are kept explicitly in `allowed`, so a finite row may exclude a kind only
after its actual count has been shown to be zero.
-/

noncomputable section
namespace Papers.RationalityTen.RootedSmallFacetCoverage

open Finset
open LiteralMaskGeometry RawFacetEmbeddingSemantics CellFacetInvariants
open MatroidChecked.FacetBoundaryEncoding
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting Papers.PolytopeFacetSurplus

def smallKind (C : Cell 10) : Nat :=
  if 4 < C.vertices.card then if cellExcess C = 1 then 3 else 2 else 1

theorem fullSmall_kind (i : Fin 6510) :
    (FacetUniverses.FullSmall.cells i).kind =
      smallKind (decodeCell (FacetUniverses.FullSmall.cells i)) :=
  FacetUniverses.FullSmall.cells_kind_correct i

/-- Complete actual coverage, retaining the exact intrinsic small-facet kind.
The only finite premise is the pointwise literal lookup certificate. -/
theorem covers_facet {d c : Nat} (P : ConvexPolytope d) (lab : P.vertices ≃ Fin 10)
    (cells : Fin c → ConcreteGrowth.Cell) (root : ConcreteGrowth.Cell)
    (hroot : WellFormed root) (allowed : Nat → Bool)
    (witness : Fin 6510 → Fin c)
    (hchecks : ∀ i, RootedCellLookup.check FacetUniverses.FullSmall.cells root cells
      allowed witness i = true)
    (F : Face P 3) (hF : facetVertexCount P F ≤ 5)
    (hallowed : allowed (smallKind (actualCell P lab F)) = true)
    (hcompatible : (actualCell P lab F).Compatible (decodeCell root)) :
    ∃ i, (cells i).kind = smallKind (actualCell P lab F) ∧
      decodeCell (cells i) = actualCell P lab F := by
  obtain ⟨i, hi⟩ := FullSmallFacetActualCoverage.covers_facet P lab F hF
  have hkind : (FacetUniverses.FullSmall.cells i).kind = smallKind (actualCell P lab F) :=
    (fullSmall_kind i).trans (congrArg smallKind hi)
  have ha : allowed (FacetUniverses.FullSmall.cells i).kind = true := by
    rw [hkind]
    exact hallowed
  obtain ⟨hk, hg⟩ := RootedCellLookupSemantics.lookup_geometry
    FacetUniverses.FullSmall.cells root cells allowed witness
    FacetUniverses.FullSmall.cells_wellFormed hroot hchecks i ha (hi.symm ▸ hcompatible)
  exact ⟨witness i, hk.trans hkind, hg.trans hi⟩

end Papers.RationalityTen.RootedSmallFacetCoverage
