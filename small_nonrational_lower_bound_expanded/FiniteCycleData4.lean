module

public import FiniteCycleCandidates

@[expose] public section

namespace Papers.RationalityTen.FiniteCycleCandidates.N4
open PolygonBoundaryCatalogue BoundarySearch
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def cells : Fin 4 → Polygon 4 := ![
  ⟨{0,1,2}, {(0,1),(0,2),(1,2)}⟩,
  ⟨{0,1,3}, {(0,1),(0,3),(1,3)}⟩,
  ⟨{0,2,3}, {(0,2),(0,3),(2,3)}⟩,
  ⟨{1,2,3}, {(1,2),(1,3),(2,3)}⟩]

def neighbors : Finset (Fin 4) := {1}
def permMaps : Fin 1 → Fin 4 → Fin 4 := ![![0,1,2,3]]
def templates : Fin 1 → Finset (Polygon 4) := fun _ => Finset.univ.image cells

theorem cells_injective : Function.Injective cells := by decide +kernel
theorem root_exact : cells 0 = triangle 4 (by decide) := by decide +kernel
theorem permMaps_injective : ∀ p, Function.Injective (permMaps p) := by decide +kernel
theorem permMaps_preserve_root : ∀ p,
    relabelPolygon (permMaps p) (triangle 4 (by decide)) = triangle 4 (by decide) := by
  decide +kernel

theorem covered_3 : ∀ f : Fin 3 → Fin 4,
    Covered cells (triangle 4 (by decide)) f := by decide +kernel

theorem neighbor_3 : ∀ f : Fin 3 → Fin 4,
    NeighborWitness cells neighbors (by decide) permMaps f := by decide +kernel

/-- There are only sixteen subfamilies of the four candidate triangles;
the actual-boundary validity conditions force the complete tetrahedron. -/
theorem valid_boundary_exact : ∀ S : Finset (Fin 4),
    valid cells S → relabelBoundary cells (Equiv.refl (Fin 4)) S = templates 0 := by
  decide +kernel

theorem normalized_classification (S : Finset (Fin 4)) (hv : valid cells S) :
    ∃ (σ : Equiv.Perm (Fin 4)) (i : Fin 1), relabelBoundary cells σ S = templates i :=
  ⟨Equiv.refl _, 0, valid_boundary_exact S hv⟩

end Papers.RationalityTen.FiniteCycleCandidates.N4
