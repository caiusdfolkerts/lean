import bier.general_construction
import bier.forster.operator_norm

/-!
# Explicit nonpolytopal Bier spheres

Theorem 1: `Bier.principal_example`, `Bier.all_labels_example`,
`Bier.self_dual_example`, and `Bier.three_dimensional_example`.

Theorem 2: `Bier.ghost_signRank_bound_fixedCard` and
`Bier.ghost_signRank_bound_arbitrary`. The final parameterized extension is
`Bier.general_allSign_construction_unrestricted`.

All definitions use actual finite complexes, convex realizations, real
matrix rank, and piecewise-linear sphere realizations. The default build
also checks `bier.audit`, which rejects any unapproved transitive axiom.
-/
