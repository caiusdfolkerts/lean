# Sharp bounds for indecomposable summands of graphical zonotopes

This project contains the full Lean4 formalisation for all principal results in my paper *Sharp bounds for indecomposable summands of graphical zonotopes*.

## Verification

If you have Elan and Git installed, run below commands from this directory.

```sh
lake exe cache get
lake build
```

## Main results

Here's a guide to help you navigate this repo! All verified theorems/propositions/corollaries are linked to their corresponding Lean4 declarations in the table below. Note declaration names use `GraphicalZonotopes`.

| Paper result | Lean statement |
| --- | --- |
| **Theorem 3.1**, p. 8 | `Path.principal_path_theorem`, `Path.PrincipalPathClaim` |
| **Theorem 4.1**, p. 11 | `sharp_direction_bounds`, `direction_bounds_polytopal` |
| **Lemma 5.1**, p. 15 | `Separator.induced_separator_capacity_finite` |
| **Theorem 5.4**, p. 18 | `Separator.positive_response_gluing_finite`, `Separator.PositiveResponseGluingConclusion`, `Separator.assembled_boundary_lift_transfer` |
| **Theorem 6.1**, p. 22 | `threeTree_classification_polytopal`, `threeTree_classification_literal`, `admissible_threeTree_lattice_witness`, `admissible_threeTree_construction` |
