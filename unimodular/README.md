# Unimodular configurations and complete fans

This project formalises the positive degree-one characterisation of complete fans and the series-parallel classification of normal matroids of deeply monotone polytopes, together with the associated lattice, toric and enumeration results described in `formalisation.md`.

## Verification

With Elan, Git and Python 3 installed, run these commands from this directory. Lean and dependency revisions are pinned in the supplied configuration.

```sh
lake exe cache get
lake build
```

The default build compiles all 800 source modules in dependency order with kernel checking enabled and checks the transitive axioms of the 191 advertised declarations. It rejects proof placeholders and axioms beyond `propext`, `Classical.choice`, and `Quot.sound`. The build uses up to eight compiler processes; allow 64 GB of memory.

## Main results

| Paper result | Lean statement |
| --- | --- |
| Theorem 1.1 / Theorem 3.1: complete fans, zero-one coefficients and connectivity | `Unimodular.AllowedBlocks.theorem_3_1`, `theorem_3_1_zero_one`, `theorem_1_1_connectivity` |
| Theorem 1.2: original-lattice normal matroid and connected series-parallel components | `Unimodular.OriginalSmoothReflexivePresentation.theorem_1_2_original_lattice_direct_sum_networks` |
| Exact minor class and cubical realisation | `Unimodular.SeriesParallel.groundSeriesParallel_iff_normalMatroid_minor`, `groundSeriesParallel_cubical_realization` |
| Proposition 5.1: explicit eight-dimensional R₁₀ example | `Unimodular.ExplicitR10.proposition_5_1` |
| Proposition 6.10: graphic section rings over arbitrary fields | `Unimodular.GraphicSectionRing.OriginalLattice.AllFields.theorem_6_10_arbitrary_lattice` |
| Theorem 7.1: sharp ray bound and equality | `Unimodular.ActualFanTheorems.theorem_7_1_bound_and_equality` |
| A₃ enumeration: 729 complete fans, 603 projective and 126 nonprojective | `Unimodular.LiteralRootCoordinates.a3_literal_complete_fan_count`, `Unimodular.LiteralA3Projectivity.literal_lattice_projective_fan_count`, `literal_nonprojective_fan_count` |

The public theorem interface is `source/verified.lean`. The source is arranged by mathematical topic under `source/unimodular` and `source/continuation`, with the necessary supporting developments alongside them. The build preserves the verified Lean module identities in a generated local workspace.

I’m still working on formalising the construction classification in Theorem 3.4 and the higher-Nₚ assertion in Corollary 6.11. I plan to release these additions in the next few days.
