# Normal–projective equivalence and the exact cube bound

This project contains the full Lean4 formalisation for all principal results in my paper *Normal–projective equivalence and the exact cube bound*.

## Verification

If you have Elan and Git installed, run below commands from this directory.

```sh
lake exe cache get
lake build
```

## Main results

Here's a guide to help you navigate this repo! All verified theorems/propositions/corollaries are linked to their corresponding Lean4 declarations in the table below. Note declaration names use `NormalProjective`.

| Paper result | Lean statement |
| --- | --- |
| Theorem 1: PN classes are exactly the connected components of the affine quotient | `CanonicalModel.Realization.pnRelated_iff_same_component` |
| Lemma 4: local bound of at most `2d` moves | `normalized_matrix_local_word`, `CanonicalModel.Realization.local_word_neighbourhood` |
| Corollary 2: every simple convex 3-polytope is PN-unique | `simple_three_pn_unique`, `simple_three_presentations_pn`, `simple_three_faceOrderIso_pn` |
| Theorem 3: upper bound with separate projective and normal counts | `CubeUpper.every_cube_exact_word` |
| Theorem 3: upper bound from an arbitrary actual face-order isomorphism | `CubeUpper.every_cube_exact_word_of_faceOrderIso` |
| Theorem 3: lower bound for every cyclic member and every target cube labelling | `CubeTargetLabels.cyclic_to_geometric_cube_lower_bound` |
| Theorem 3: exact largest distance `2d - 3`, for every `d ≥ 2` | `CubeTargetLabels.geometric_largest_PN_distance` |
| Correction to the auxiliary polarity identity | `PolarCorrection.boundary_origin_counterexample` |
