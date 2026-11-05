module

public import FiniteCycleData5

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FiniteCycleCandidates.N5

theorem covered_3 : ∀ f : Fin 3 → Fin 5,
    Covered cells (triangle 5 (by decide)) f := by decide +kernel
 theorem neighbor_3 : ∀ f : Fin 3 → Fin 5,
    NeighborWitness cells neighbors (by decide) permMaps f := by decide +kernel

end Papers.RationalityTen.FiniteCycleCandidates.N5
