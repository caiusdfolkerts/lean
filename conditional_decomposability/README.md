# The sharp vertex bound for conditional decomposability

This project formalises the principal results of Caius Folkerts’s *The sharp vertex bound for conditional decomposability*. The source includes the supporting mathematics needed for the stated results.

## Verification

With Elan and Git installed, run these commands from this directory. The toolchain and dependency revisions are pinned in the supplied configuration.

```sh
lake exe cache get
lake build
```

The default build includes the mathematical source and checks that the imported project theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. Downloading the library cache is not itself a proof check.

## Main results

Unless otherwise qualified, declaration names use the namespace `Papers.Polytopes`.

| Paper result | Lean statement |
| --- | --- |
| Theorem 1: universal lower bound and all-dimensional attainment | `conditional_decomposability_sharp` |
| The literal least vertex count | `conditional_vertex_count_isLeast` |
| Decomposability below the threshold is determined by the face lattice | `decomposability_determined_by_face_lattice_below_threshold` |
| Decomposability is simultaneous in face-equivalent realizations below the threshold | `decomposable_iff_of_face_iso_below_threshold` |
| Sharp examples in every dimension | `conditional_decomposability_attainment` |
