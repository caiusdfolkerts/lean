# Sharp bounds for indecomposable summands of graphical zonotopes

This project formalises the principal results of Caius Folkerts’s *Sharp bounds for indecomposable summands of graphical zonotopes*. The source includes the supporting mathematics needed for the stated results.

## Verification

With Elan and Git installed, run these commands from this directory. The toolchain and dependency revisions are pinned in the supplied configuration.

```sh
lake exe cache get
lake build
```

The default build includes the mathematical source and checks that the imported project theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. Downloading the library cache is not itself a proof check.

## Main results

Unless otherwise qualified, declaration names use the namespace `GraphicalZonotopes`.

| Paper result | Lean statement |
| --- | --- |
| **Theorem 3.1**, p. 8 | `Path.principal_path_theorem`, `Path.PrincipalPathClaim` |
| **Theorem 4.1**, p. 11 | `sharp_direction_bounds`, `direction_bounds_polytopal` |
| **Lemma 5.1**, p. 15 | `Separator.induced_separator_capacity_finite` |
| **Theorem 5.4**, p. 18 | `Separator.positive_response_gluing_finite`, `Separator.PositiveResponseGluingConclusion`, `Separator.assembled_boundary_lift_transfer` |
| **Theorem 6.1**, p. 22 | `threeTree_classification_polytopal`, `threeTree_classification_literal`, `admissible_threeTree_lattice_witness`, `admissible_threeTree_construction` |
