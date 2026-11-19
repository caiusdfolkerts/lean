module

public import FiniteCycleCandidates

@[expose] public section

namespace Papers.RationalityTen.FiniteCycleCandidates
open MatroidChecked PolygonBoundaryCatalogue
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace N5
def cellTable : LiteralLookup (Polygon 5) := (.node 8 (.node 4 (.node 2 (.node 1 (.leaf (⟨{0,1,2},{(0,1),(0,2),(1,2)}⟩)) (.leaf (⟨{0,1,3},{(0,1),(0,3),(1,3)}⟩))) (.node 3 (.leaf (⟨{0,1,4},{(0,1),(0,4),(1,4)}⟩)) (.leaf (⟨{0,2,3},{(0,2),(0,3),(2,3)}⟩)))) (.node 6 (.node 5 (.leaf (⟨{0,2,4},{(0,2),(0,4),(2,4)}⟩)) (.leaf (⟨{0,3,4},{(0,3),(0,4),(3,4)}⟩))) (.node 7 (.leaf (⟨{1,2,3},{(1,2),(1,3),(2,3)}⟩)) (.leaf (⟨{1,2,4},{(1,2),(1,4),(2,4)}⟩))))) (.node 12 (.node 10 (.node 9 (.leaf (⟨{1,3,4},{(1,3),(1,4),(3,4)}⟩)) (.leaf (⟨{2,3,4},{(2,3),(2,4),(3,4)}⟩))) (.node 11 (.leaf (⟨{0,1,3,4},{(0,1),(0,4),(1,3),(3,4)}⟩)) (.leaf (⟨{0,1,3,4},{(0,1),(0,3),(1,4),(3,4)}⟩)))) (.node 14 (.node 13 (.leaf (⟨{0,2,3,4},{(0,2),(0,4),(2,3),(3,4)}⟩)) (.leaf (⟨{0,2,3,4},{(0,2),(0,3),(2,4),(3,4)}⟩))) (.node 15 (.leaf (⟨{1,2,3,4},{(1,2),(1,4),(2,3),(3,4)}⟩)) (.leaf (⟨{1,2,3,4},{(1,2),(1,3),(2,4),(3,4)}⟩))))))
def cells (i : Fin 16) : Polygon 5 := cellTable.get i.val

def neighbors : Finset (Fin 16) := {1,10}
def permMaps : Fin 2 → Fin 5 → Fin 5 := ![![0,1,2,3,4],
  ![0,1,2,4,3]]

theorem cells_injective : Function.Injective cells := by decide +kernel
 theorem root_exact : cells 0 = triangle 5 (by decide) := by decide +kernel
 theorem permMaps_injective : ∀ p, Function.Injective (permMaps p) := by decide +kernel
 theorem permMaps_preserve_root : ∀ p,
    relabelPolygon (permMaps p) (triangle 5 (by decide)) = triangle 5 (by decide) := by
  decide +kernel

end N5
end Papers.RationalityTen.FiniteCycleCandidates
