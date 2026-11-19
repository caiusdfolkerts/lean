module

public import ActualLeafCertificates
public import RootedKindedActualEncoding

@[expose] public section

/-!
# From finite rooted classifications to actual rational realizations

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

/-- A complete finite classification and the checked disposition of all
its leaves. No polytope or realizability proposition appears in these data. -/
structure FiniteClassification {n : Nat} (cells : Fin n → ConcreteGrowth.Cell)
    (quota : Nat → Nat) (root : Fin n) where
  wellFormed : ∀ i, WellFormed (cells i)
  generatorCount : Nat
  frames : Fin generatorCount → BoundaryGeneratorFrames.BoundaryFrame cells
  leafCount : Nat
  leaves : Fin leafCount → List (Fin n)
  rawLeaves : Fin leafCount → List ConcreteGrowth.Cell
  raw_exact : ∀ j, (leaves j).map cells = rawLeaves j
  certificates : Fin leafCount → RawLeafCertificate.Certificate
  checked : ∀ j, RawLeafCertificate.check quota (rawLeaves j) (certificates j) = true
  complete : ∀ B : List (Fin n),
    GrowthRenaming.Target
      (fun a => SparseGrowthDAG.has (ConcreteGrowth.ridgeList cells a))
      (fun a b => ConcreteGrowth.compatible (cells a) (cells b))
      (fun a => (cells a).kind) quota B → root ∈ B →
    ∃ j word, (leaves j).Nodup ∧
      GrowthDAG.Same (SparseGrowthDAG.family (leaves j))
        (SparseGrowthDAG.family (OrbitGrowthDAG.applyWord
          (fun f => (frames f).toBoundaryRenaming wellFormed) word B))

/-- Constructor for a classification that requires no relabeling generators.
The empty word acts as the identity, so the finite proof is used verbatim. -/
def FiniteClassification.of_identity {n k : Nat}
    (cells : Fin n → ConcreteGrowth.Cell) (quota : Nat → Nat) (root : Fin n)
    (wellFormed : ∀ i, WellFormed (cells i))
    (leaves : Fin k → List (Fin n)) (rawLeaves : Fin k → List ConcreteGrowth.Cell)
    (raw_exact : ∀ j, (leaves j).map cells = rawLeaves j)
    (certificates : Fin k → RawLeafCertificate.Certificate)
    (checked : ∀ j, RawLeafCertificate.check quota (rawLeaves j) (certificates j) = true)
    (complete : ∀ B : List (Fin n),
      GrowthRenaming.Target
        (fun a => SparseGrowthDAG.has (ConcreteGrowth.ridgeList cells a))
        (fun a b => ConcreteGrowth.compatible (cells a) (cells b))
        (fun a => (cells a).kind) quota B → root ∈ B →
      ∃ j, (leaves j).Nodup ∧
        GrowthDAG.Same (SparseGrowthDAG.family (leaves j)) (SparseGrowthDAG.family B)) :
    FiniteClassification cells quota root where
  wellFormed := wellFormed
  generatorCount := 0
  frames := Fin.elim0
  leafCount := k
  leaves := leaves
  rawLeaves := rawLeaves
  raw_exact := raw_exact
  certificates := certificates
  checked := checked
  complete := by
    intro B hB hroot
    obtain ⟨j, hnodup, hsame⟩ := complete B hB hroot
    exact ⟨j, [], hnodup, hsame⟩

theorem nonsimple_neighbors {P : ConvexPolytope 4} (hP : P.IsFullDim)
    (h : ∀ v : P.vertices, ¬ IsSimpleVertex P v) :
    ∀ v : P.vertices, (Papers.PolytopeVertexCone.actualNeighbors P v.val).card ≠ 4 := by
  intro v hv
  apply h v
  change (polytopeGraph P).degree v = P.dim
  rw [← NineBipyramidIncidence.vertexGraph_eq_polytopeGraph,
    MatroidChecked.IncidentFacetSimplicity.degree_eq_actual_neighbors, hv, hP]

/-- A finite classification is sufficient once the supplied complete
encoding has its precise quota and selected root. -/
theorem rationallyRealizable_of_encoding {n : Nat}
    (hvalid : ∀ j, j < targetCount → ValidTarget j)
    (P : ConvexPolytope 4) (hP : P.IsFullDim)
    (hnonsimple : ∀ v : P.vertices, ¬ IsSimpleVertex P v)
    (lab : P.vertices ≃ Fin 10) (cells : Fin n → ConcreteGrowth.Cell)
    (quota : Nat → Nat) (root : Fin n)
    (classification : FiniteClassification cells quota root)
    (E : Encoding P lab (fun i => decodeCell (cells i)))
    (hroot : root ∈ E.family)
    (hquota : ∀ t, (E.family.filter fun i => (cells i).kind = t).card = quota t) :
    RationallyRealizable P := by
  have htarget := LiteralMaskGeometry.actual_literal_target cells
    classification.wellFormed E hP quota (fun k => (hquota k).le)
  have hcomplete := classification.complete E.family.toList htarget
    (Finset.mem_toList.mpr hroot)
  exact ActualLeafCertificates.rationallyRealizable_of_classification
    hvalid P hP (nonsimple_neighbors hP hnonsimple) lab cells
    classification.wellFormed E classification.frames classification.leaves
    classification.rawLeaves classification.raw_exact quota hquota
    classification.certificates classification.checked hcomplete

/-- The complete actual-to-finite bridge. The sole coverage premise is a
finite statement about every embedded compatible local template, which the
independent placement certificates check. Normalization and facet quotas
are derived here for the original polytope. -/
theorem rationallyRealizable_of_templates {n : Nat} {T : Type*}
    (hvalid : ∀ j, j < targetCount → ValidTarget j)
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
    RationallyRealizable P := by
  obtain ⟨lab, E, hroot, htag⟩ := RootedKindedActualEncoding.normalized_encoding_of_templates
    size templates tag P lab₀ cells root F rootType loc hloc rootEmbedding
    hrootCell hrootKind assignment hlocal eligible heligible hfinite
  obtain ⟨_, hquota⟩ := RootedKindedActualEncoding.literal_target_of_tag_counts
    cells E hP classification.wellFormed
    (fun G => if G = F then 0 else tag (assignment G)) htag quota hcounts
  exact rationallyRealizable_of_encoding hvalid P hP hnonsimple lab cells quota root
    classification E ((E.mem_family root).mpr ⟨F, hroot⟩) hquota

end Papers.RationalityTen.RootedFamilyClosure
