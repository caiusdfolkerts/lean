# Rank-three obstructions to coordinate projection volumes

This project formalises the principal results of Caius Folkerts’s *Rank-three obstructions to coordinate projection volumes*. The source includes the supporting mathematics needed for the stated results.

## Verification

With Elan and Git installed, run these commands from this directory. The toolchain and dependency revisions are pinned in the supplied configuration.

```sh
lake exe cache get
lake build
```

The default build includes the mathematical source and checks that the imported project theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. Downloading the library cache is not itself a proof check.

## Main results

Unless otherwise qualified, declaration names use the namespace `RankThreeProjection`.

| Paper result | Lean statement |
| --- | --- |
| Theorem 1.1, all conclusions | `theorem11` |
| Theorem 1.1 in canonical Euclidean coordinates | `theorem11_euclidean` |
| Rank-three exclusion from the actual closure | `rank_three_projection_exclusion` |
| Direct limit statement for strict counterexamples | `rank_three_limit_strict_counterexamples` |
| Nonempty open family in every dimension at least five | `exists_open_counterexamples` |
| Proposition 4.2, with full-dimensional rigidity supplied | `full_dimensional_obstruction` |
| Theorem 3.1, closure formula for every `1 ≤ k < n` | `theorem31` |
| Theorem 3.1 with the exact affine-dimension bound | `theorem31_with_dimension` |
| Replacement of every marked representation with the dimension bound | `theorem31_renormalize_dimension` |
| Theorem 3.1 with Euclidean bodies, volumes, and dimension | `theorem31_euclidean` |
| Theorem 3.1 with unrestricted Euclidean representations | `theorem31_euclidean_closure` |
| Replacement of every Euclidean representation with the dimension bound | `theorem31_euclidean_renormalize_dimension` |
| Signature as positive, negative, and zero diagonal counts | `signature_iff_diagonal_sign_counts` |
