# Compatibility and realization of coordinate projection areas

This project contains the full Lean4 formalisation for all principal results in my paper *Compatibility and realization of coordinate projection areas*.

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
| Theorem 1.1: nonapproximation, with every four-coordinate restriction realized | `ProjectionAreaPaper.positive_rank_three_obstruction` |
| Proposition 2.3: compatibility with positivity only on the two boundary quartets | `ProjectionAreaPaper.boundary_compatibility_of_local_positivity` |
| Corollary 2.4: at most three boundary quartets, with sharpness | `ProjectionAreaMixedGeometry.boundary_quartets_bound_sharp` |
| Corollary 2.4: unique partition into two and three labels | `ProjectionAreaMixedGeometry.boundary_quartets_unique_extension` |
| Corollary 2.4: any five selected labels in an arbitrary ambient dimension | `ProjectionAreaPaper.selected_boundary_quartets_card_le_three`, `selected_boundary_quartets_unique_extension` |
| Corollary 2.5: exact nonrealizability | `ProjectionAreaPaper.positive_rank_le_three_not_realizable` |
| Proposition 3.2: prescribed widths and exact prism families | `ProjectionAreaEscape.exists_prescribed_width_polytope_exact_prisms` |
| §3, equation (4): the exact area formula | `ProjectionAreaEscape.ExactPrism.coordinate_area_prism` |
| Theorems 1.2 and 3.3: escape characterization | `ProjectionAreaPaper.escapeCone_eq_divergingDiameterLimits` |
| Theorems 1.2 and 3.3: closure identity | `ProjectionAreaPaper.closure_realizationLocus_eq_union_escapeCone` |
| Theorem 3.3: full-dimensional centrally symmetric polytope approximants | `ProjectionAreaPaper.mem_escapeCone_iff_exists_full_dimensional_symmetric_sequence` |
| Theorem 3.3: closedness of the escape cone | `ProjectionAreaPaper.escapeCone_isClosed` |
| Theorem 4.1: exact strict realization, arbitrary diameter, and actual vertex bound | `ProjectionAreaStrict.strict_weighted_realization_with_vertex_bound` |
| Theorem 1.2: the strict clause including low-dimensional zero data | `ProjectionAreaStrict.strict_nonnegative_weighted_realization_with_vertex_bound` |
| Corollary 5.2: weighted metric obstruction, including vanishing weights | `ProjectionAreaRankThree.PositiveHollowMatrix.weighted_triangles_obstruction` |
| Corollary 5.3: an open family of nonrealizable strict quartets | `ProjectionAreaPaper.exists_open_nonrealizable_strict_quartets` |
| Proposition 6.1: general zero-row reduction under the local spectral hypothesis | `ProjectionAreaSpectralZero.local_spectral_zero_reduction` |
| Theorem 6.2: the complete nonnegative rank-at-most-three classification | `ProjectionAreaPaper.NonnegativeHollowMatrix.rank_at_most_three_classification` |
