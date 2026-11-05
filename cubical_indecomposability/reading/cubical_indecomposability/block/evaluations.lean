import cubical_indecomposability.block.data

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CubicalIndecomposability.Block

/-- All homogeneous denominators are positive. -/
theorem homogeneous_last_pos : ∀ v : Fin 32, 0 < q v 4 := by decide +kernel

/-- Exact support inequalities and their equality loci for all 24×32 pairs. -/
theorem supportData : ∀ (f : Fin 24) (v : Fin 32),
    0 ≤ slackNumerator f v ∧ (slackNumerator f v = 0 ↔ incident f v) := by
  decide +kernel

end CubicalIndecomposability.Block
