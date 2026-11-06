# Unimodular configurations and complete fans

This project contains the full Lean4 formalisation for the principal results in my paper *Unimodular configurations and complete fans*. I’m still working on the remaining results, which I expect to be ready in a few days.

## Verification

If you have Elan and Git installed, run below commands from this directory.

```sh
lake exe cache get
lake build
```

## Main results

Here's a guide to help you navigate this repo! All verified theorems/propositions/corollaries are linked to their corresponding Lean4 declarations in the table below.

| Paper result | Lean statement |
| --- | --- |
| Theorem 1.1 / Theorem 3.1: complete fans, zero-one coefficients and connectivity | `Unimodular.AllowedBlocks.theorem_3_1`, `theorem_3_1_zero_one`, `theorem_1_1_connectivity` |
| Theorem 1.2: original-lattice normal matroid and connected series-parallel components | `Unimodular.OriginalSmoothReflexivePresentation.theorem_1_2_original_lattice_direct_sum_networks` |
| Exact minor class and cubical realisation | `Unimodular.SeriesParallel.groundSeriesParallel_iff_normalMatroid_minor`, `groundSeriesParallel_cubical_realization` |
| Proposition 5.1: explicit eight-dimensional R₁₀ example | `Unimodular.ExplicitR10.proposition_5_1` |
| Proposition 6.10: graphic section rings over arbitrary fields | `Unimodular.GraphicSectionRing.OriginalLattice.AllFields.theorem_6_10_arbitrary_lattice` |
| Theorem 7.1: sharp ray bound and equality | `Unimodular.ActualFanTheorems.theorem_7_1_bound_and_equality` |
| A₃ enumeration: 729 complete fans, 603 projective and 126 nonprojective | `Unimodular.LiteralRootCoordinates.a3_literal_complete_fan_count`, `Unimodular.LiteralA3Projectivity.literal_lattice_projective_fan_count`, `literal_nonprojective_fan_count` |
