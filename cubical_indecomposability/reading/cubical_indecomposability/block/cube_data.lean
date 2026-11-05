import cubical_indecomposability.block.data

/-! Exact integer arithmetic and finite incidences, checked by Lean's kernel.
`decide +kernel` below proves closed propositions by reduction.  It invokes no native
oracle and introduces no mathematical assumptions.  Row lemmas keep the
kernel reduction and subsequent rebuilds small.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CubicalIndecomposability.Block

theorem cubeVertex_injective : ∀ f : Fin 24, Function.Injective (cubeVertex f) := by decide +kernel

theorem cubeVertex_image : ∀ f : Fin 24, Finset.univ.image (cubeVertex f) = facetLabels f := by decide +kernel

theorem neighbor_incidence : ∀ (f : Fin 24) (k : Fin 6) (b : Fin 8),
    incident (neighborFacet f k) (cubeVertex f b) ↔ squareBit k b := by decide +kernel

theorem neighborFacet_ne : ∀ (f : Fin 24) (k : Fin 6), neighborFacet f k ≠ f := by decide +kernel

end CubicalIndecomposability.Block
