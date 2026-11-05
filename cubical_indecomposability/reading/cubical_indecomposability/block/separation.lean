import cubical_indecomposability.block.separating_witness

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CubicalIndecomposability.Block

/-- Distinct labels are strictly separated by one active supporting form. -/
theorem separatingData : ∀ (v w : Fin 32), v ≠ w →
    incident (separatingWitness v w) v ∧ ¬incident (separatingWitness v w) w := by
  decide +kernel

end CubicalIndecomposability.Block
