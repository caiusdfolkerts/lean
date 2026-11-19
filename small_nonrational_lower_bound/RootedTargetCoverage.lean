module

public import RootedFamilyClosure
public import ActualLeafTargetCoverage

@[expose] public section

/-!
# Full actual terminal coverage for rooted classifications

The finite-family interface contains only finite cell, permutation, leaf,
and certificate statements. The theorem below derives its target from an
actual convex polytope, normalizes the distinguished facet, preserves all
facet-kind counts, and applies the already proved geometric leaf soundness.
-/

noncomputable section
namespace Papers.RationalityTen.RootedFamilyClosure

open Finset
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting
open MatroidChecked.FacetBoundaryEncoding
open ActualFacetCatalogueTransport LiteralMaskGeometry
open Nonrational.TerminalData Nonrational.TerminalVerification

/-- A finite classification is sufficient once the supplied complete
encoding has its precise quota and selected root. -/
theorem hasTerminal_of_encoding {n : Nat}
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (lab : P.vertices ≃ Fin 10) (cells : Fin n → ConcreteGrowth.Cell)
    (quota : Nat → Nat) (root : Fin n)
    (classification : FiniteClassification cells quota root)
    (E : Encoding P lab (fun i => decodeCell (cells i)))
    (hroot : root ∈ E.family)
    (hquota : ∀ t, (E.family.filter fun i => (cells i).kind = t).card = quota t) :
    ActualLeafTargetCoverage.HasTerminal P := by
  have htarget := LiteralMaskGeometry.actual_literal_target cells
    classification.wellFormed E hP quota (fun k => (hquota k).le)
  have hcomplete := classification.complete E.family.toList htarget
    (Finset.mem_toList.mpr hroot)
  exact ActualLeafTargetCoverage.hasTerminal_of_classification
    P hP (nonsimple_neighbors hP hnonsimple) lab cells
    classification.wellFormed E classification.frames classification.leaves
    classification.rawLeaves classification.raw_exact quota hquota
    classification.certificates classification.checked hcomplete

/-- The complete actual-to-finite bridge. The sole coverage premise is a
finite statement about every embedded compatible local template, which the
independent placement certificates check. Normalization and facet quotas
are derived here for the original polytope. -/
theorem hasTerminal_of_templates {n : Nat} {T : Type*}
    (size : T → Nat)
    (templates : (t : T) → Finset (PolygonBoundaryCatalogue.Polygon (size t)))
    (tag : T → Nat)
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (lab₀ : P.vertices ≃ Fin 10) (cells : Fin n → ConcreteGrowth.Cell)
    (quota : Nat → Nat) (root : Fin n)
    (classification : FiniteClassification cells quota root)
    (F : Face P 3) (rootType : T)
    (loc : (facePolytope P F.val.isFace).vertices ≃ Fin (size rootType))
    (hloc : polygonBoundary (facePolytope P F.val.isFace) loc = templates rootType)
    (rootEmbedding : Fin (size rootType) ↪ Fin 10)
    (hrootCell : mapCell rootEmbedding (cellOfBoundary (templates rootType)) =
      decodeCell (cells root))
    (hrootKind : (cells root).kind = 0)
    (assignment : Face P 3 → T)
    (hlocal : ∀ G : Face P 3,
      ∃ localLabel : (facePolytope P G.val.isFace).vertices ≃ Fin (size (assignment G)),
        polygonBoundary (facePolytope P G.val.isFace) localLabel = templates (assignment G))
    (eligible : T → Prop)
    (heligible : ∀ G : Face P 3, G ≠ F → eligible (assignment G))
    (hfinite : ∀ t, eligible t → ∀ f : Fin (size t) ↪ Fin 10,
      (mapCell f (cellOfBoundary (templates t))).Compatible (decodeCell (cells root)) →
        ∃ i, (cells i).kind = tag t ∧
          decodeCell (cells i) = mapCell f (cellOfBoundary (templates t)))
    (hcounts : ∀ k, (Finset.univ.filter fun G : Face P 3 =>
      (if G = F then 0 else tag (assignment G)) = k).card = quota k) :
    ActualLeafTargetCoverage.HasTerminal P := by
  obtain ⟨lab, E, hroot, htag⟩ := RootedKindedActualEncoding.normalized_encoding_of_templates
    size templates tag P lab₀ cells root F rootType loc hloc rootEmbedding
    hrootCell hrootKind assignment hlocal eligible heligible hfinite
  obtain ⟨_, hquota⟩ := RootedKindedActualEncoding.literal_target_of_tag_counts
    cells E hP classification.wellFormed
    (fun G => if G = F then 0 else tag (assignment G)) htag quota hcounts
  exact hasTerminal_of_encoding P hP hnonsimple lab cells quota root
    classification E ((E.mem_family root).mpr ⟨F, hroot⟩) hquota

#print axioms hasTerminal_of_templates
end Papers.RationalityTen.RootedFamilyClosure
