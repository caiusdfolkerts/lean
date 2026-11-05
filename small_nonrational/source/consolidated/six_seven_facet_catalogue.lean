module
public import ConcreteRootCoverageSmall
public import FiniteCycleN6K3
public import FiniteCycleN6K4
public import FiniteCycleN6K5
public import FiniteCycleN7K3
public import FiniteCycleN7K4
public import FiniteCycleN7K5
public import FiniteCycleN7K6
public import ActualSmallFacetClassification
public import PolygonN6Classification
public import PolygonN7Classification
public import ActualFacetCatalogueTransport

/-! Canonical source bundle; each original file retains its own scopes. -/

section BundlePart0
/- Source: ConcreteRootCoverage.lean -/











@[expose] public section
noncomputable section

namespace Papers.RationalityTen.FiniteCycleCandidates
open ActualPolygonBoundary PolygonBoundaryCatalogue

namespace N6

theorem covers_rooted_cycles :
    CoversRootedCycles cells (rootTriangle 6 (by decide)) := by
  intro k hk hkn f h
  have cases : k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases cases with rfl | rfl | rfl
  · exact covered_3 f f.injective h
  · exact covered_4 f f.injective h
  · exact covered_5 f f.injective h

theorem normalizes_root_neighbor :
    NormalizesRootNeighbor cells neighbors (by decide : 3 ≤ 6) := by
  intro k hk hkn f hcompat hedge
  have cases : k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases cases with rfl | rfl | rfl
  · obtain ⟨a, i, hi, heq⟩ := neighbor_3 f f.injective hcompat hedge
    let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective (permMaps a)
      ⟨permMaps_injective a, Finite.surjective_of_injective (permMaps_injective a)⟩
    refine ⟨σ, ?_, i, hi, heq⟩
    exact permMaps_preserve_root a
  · obtain ⟨a, i, hi, heq⟩ := neighbor_4 f f.injective hcompat hedge
    let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective (permMaps a)
      ⟨permMaps_injective a, Finite.surjective_of_injective (permMaps_injective a)⟩
    refine ⟨σ, ?_, i, hi, heq⟩
    exact permMaps_preserve_root a
  · obtain ⟨a, i, hi, heq⟩ := neighbor_5 f f.injective hcompat hedge
    let σ : Equiv.Perm (Fin 6) := Equiv.ofBijective (permMaps a)
      ⟨permMaps_injective a, Finite.surjective_of_injective (permMaps_injective a)⟩
    refine ⟨σ, ?_, i, hi, heq⟩
    exact permMaps_preserve_root a

end N6

namespace N7

theorem covers_rooted_cycles :
    CoversRootedCycles cells (rootTriangle 7 (by decide)) := by
  intro k hk hkn f h
  have cases : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact covered_3 f f.injective h
  · exact covered_4 f f.injective h
  · exact covered_5 f f.injective h
  · exact covered_6 f f.injective h

theorem normalizes_root_neighbor :
    NormalizesRootNeighbor cells neighbors (by decide : 3 ≤ 7) := by
  intro k hk hkn f hcompat hedge
  have cases : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · obtain ⟨a, i, hi, heq⟩ := neighbor_3 f f.injective hcompat hedge
    let σ : Equiv.Perm (Fin 7) := Equiv.ofBijective (permMaps a)
      ⟨permMaps_injective a, Finite.surjective_of_injective (permMaps_injective a)⟩
    refine ⟨σ, ?_, i, hi, heq⟩
    exact permMaps_preserve_root a
  · obtain ⟨a, i, hi, heq⟩ := neighbor_4 f f.injective hcompat hedge
    let σ : Equiv.Perm (Fin 7) := Equiv.ofBijective (permMaps a)
      ⟨permMaps_injective a, Finite.surjective_of_injective (permMaps_injective a)⟩
    refine ⟨σ, ?_, i, hi, heq⟩
    exact permMaps_preserve_root a
  · obtain ⟨a, i, hi, heq⟩ := neighbor_5 f f.injective hcompat hedge
    let σ : Equiv.Perm (Fin 7) := Equiv.ofBijective (permMaps a)
      ⟨permMaps_injective a, Finite.surjective_of_injective (permMaps_injective a)⟩
    refine ⟨σ, ?_, i, hi, heq⟩
    exact permMaps_preserve_root a
  · obtain ⟨a, i, hi, heq⟩ := neighbor_6 f f.injective hcompat hedge
    let σ : Equiv.Perm (Fin 7) := Equiv.ofBijective (permMaps a)
      ⟨permMaps_injective a, Finite.surjective_of_injective (permMaps_injective a)⟩
    refine ⟨σ, ?_, i, hi, heq⟩
    exact permMaps_preserve_root a

end N7

end Papers.RationalityTen.FiniteCycleCandidates

end
end
end BundlePart0

section BundlePart1
/- Source: ActualSixFacetClassification.lean -/






@[expose] public section

/-! Exact complete polygon-boundary classification of every actual six-vertex three-polytope. -/
noncomputable section
namespace Papers.RationalityTen.ActualSmallFacetClassification
open Finset
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting
open ActualPolygonBoundary ActualFaceTransport
variable {d : ℕ}

theorem six_vertex_classification (P : ConvexPolytope d) (hP : P.dim = 3)
    (hn : P.vertices.card = 6) :
    ∃ (lab : P.vertices ≃ Fin 6) (i : Fin 7),
      (Finset.univ : Finset (Face P 2)).image (polygon P lab) =
        FiniteCycleCandidates.N6.templates i :=
  actual_classification_of_finite P hP hn (by decide) (by decide)
    FiniteCycleCandidates.N6.cells 0 FiniteCycleCandidates.N6.neighbors
    FiniteCycleCandidates.N6.templates
    FiniteCycleCandidates.N6.cells_injective FiniteCycleCandidates.N6.root_exact
    FiniteCycleCandidates.N6.covers_rooted_cycles FiniteCycleCandidates.N6.normalizes_root_neighbor
    ConcretePolygonClassification.N6.normalized_classification

end Papers.RationalityTen.ActualSmallFacetClassification

end
end
end BundlePart1

section BundlePart2
/- Source: ActualSixSevenFacetClassification.lean -/








@[expose] public section

/-!
# Complete actual facet catalogues through seven vertices

The finite certificates classify complete polygon boundaries. These
wrappers return actual vertex labelings and preserve every polygon and
edge. The final dependent catalogue is the local input to the ambient
four-polytope cell coverage theorem.
-/

noncomputable section
namespace Papers.RationalityTen.ActualSmallFacetClassification

open Finset
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open Papers.Polytopes Papers.PolytopeFaceCounting
open ActualPolygonBoundary ActualFaceTransport
open ActualFacetCatalogueTransport
open Papers.PolytopeIncidenceCounting

variable {d : ℕ}

theorem seven_vertex_classification (P : ConvexPolytope d) (hP : P.dim = 3)
    (hn : P.vertices.card = 7) :
    ∃ (lab : P.vertices ≃ Fin 7) (i : Fin 34),
      (Finset.univ : Finset (Face P 2)).image (polygon P lab) =
        FiniteCycleCandidates.N7.templates i :=
  actual_classification_of_finite P hP hn (by decide) (by decide)
    FiniteCycleCandidates.N7.cells 0 FiniteCycleCandidates.N7.neighbors
    FiniteCycleCandidates.N7.templates
    FiniteCycleCandidates.N7.cells_injective FiniteCycleCandidates.N7.root_exact
    FiniteCycleCandidates.N7.covers_rooted_cycles FiniteCycleCandidates.N7.normalizes_root_neighbor
    ConcretePolygonClassification.N7.normalized_classification

/-- The complete set of three-polytope types with four through seven vertices. -/
inductive SmallFacetType where
  | tetrahedron
  | five (i : Fin 2)
  | six (i : Fin 7)
  | seven (i : Fin 34)
  deriving DecidableEq, Fintype

namespace SmallFacetType

def size : SmallFacetType → ℕ
  | .tetrahedron => 4
  | .five _ => 5
  | .six _ => 6
  | .seven _ => 7

def template : (t : SmallFacetType) → Finset (PolygonBoundaryCatalogue.Polygon t.size)
  | .tetrahedron => FiniteCycleCandidates.N4.templates 0
  | .five i => FiniteCycleCandidates.N5.templates i
  | .six i => FiniteCycleCandidates.N6.templates i
  | .seven i => FiniteCycleCandidates.N7.templates i

end SmallFacetType

/-- Exhaustive classification of every actual three-polytope on at most
seven vertices, in arbitrary ambient Euclidean dimension. -/
theorem at_most_seven_vertex_classification (P : ConvexPolytope d)
    (hP : P.dim = 3) (hn : P.vertices.card ≤ 7) :
    ∃ t : SmallFacetType, ∃ lab : P.vertices ≃ Fin t.size,
      polygonBoundary P lab = t.template := by
  have hmin := actual_vertices_card_gt_dim P
  rw [hP] at hmin
  have hcases : P.vertices.card = 4 ∨ P.vertices.card = 5 ∨
      P.vertices.card = 6 ∨ P.vertices.card = 7 := by omega
  rcases hcases with h4 | h5 | h6 | h7
  · obtain ⟨lab, i, hi⟩ := four_vertex_classification P hP h4
    have hi0 : i = 0 := Fin.eq_zero i
    subst i
    exact ⟨.tetrahedron, lab, hi⟩
  · obtain ⟨lab, i, hi⟩ := five_vertex_classification P hP h5
    exact ⟨.five i, lab, hi⟩
  · obtain ⟨lab, i, hi⟩ := six_vertex_classification P hP h6
    exact ⟨.six i, lab, hi⟩
  · obtain ⟨lab, i, hi⟩ := seven_vertex_classification P hP h7
    exact ⟨.seven i, lab, hi⟩

/-- Each actual three-face with at most seven vertices has one of the
complete local templates used by the ambient cell universe. -/
theorem facet_local_template (P : ConvexPolytope d) (F : Face P 3)
    (hF : Nat.card (VerticesOn P F.val.carrier) ≤ 7) :
    ∃ t : SmallFacetType,
      ∃ lab : (facePolytope P F.val.isFace).vertices ≃ Fin t.size,
        polygonBoundary (facePolytope P F.val.isFace) lab = t.template := by
  apply at_most_seven_vertex_classification
  · change faceDim (facePolytope P F.val.isFace).toSet = 3
    rw [facePolytope_toSet]
    exact F.property
  · have hc : (facePolytope P F.val.isFace).vertices.card =
        Nat.card (VerticesOn P F.val.carrier) := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
        (Nat.card_congr (faceVerticesEquiv P F.val.isFace)).symm
    exact hc.trans_le hF

end Papers.RationalityTen.ActualSmallFacetClassification

end
end
end BundlePart2
