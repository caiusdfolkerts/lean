# The sharp vertex bound for conditional decomposability

This project contains the full Lean4 formalisation for all principal results in my paper *The sharp vertex bound for conditional decomposability*.

## Verification

If you have Elan and Git installed, run below commands from this directory.

```sh
lake exe cache get
lake build
```

## Main results

Here's a guide to help you navigate this repo! All verified theorems/propositions/corollaries are linked to their corresponding Lean4 declarations in the table below. Note declaration names use `Papers.Polytopes`.

| Paper result | Lean statement |
| --- | --- |
| Theorem 1: universal lower bound and all-dimensional attainment | `conditional_decomposability_sharp` |
| The literal least vertex count | `conditional_vertex_count_isLeast` |
| Decomposability below the threshold is determined by the face lattice | `decomposability_determined_by_face_lattice_below_threshold` |
| Decomposability is simultaneous in face-equivalent realizations below the threshold | `decomposable_iff_of_face_iso_below_threshold` |
| Sharp examples in every dimension | `conditional_decomposability_attainment` |
