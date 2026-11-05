# Normal–projective equivalence and the exact cube bound

This project formalises the principal results of Caius Folkerts’s *Normal–projective equivalence and the exact cube bound*. The source includes the supporting mathematics needed for the stated results.

## Verification

With Elan and Git installed, run these commands from this directory. The toolchain and dependency revisions are pinned in the supplied configuration.

```sh
lake exe cache get
lake build
```

The default build includes the mathematical source and checks that the imported project theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. Downloading the library cache is not itself a proof check.

## Main results

Unless otherwise qualified, declaration names use the namespace `NormalProjective`.

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
