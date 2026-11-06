# Rank-three obstructions to coordinate projection volumes

This project contains the full Lean4 formalisation for all principal results in my paper *Rank-three obstructions to coordinate projection volumes*.

## Verification

If you have Elan and Git installed, run below commands from this directory.

```sh
lake exe cache get
lake build
```

## Main results

Here's a guide to help you navigate this repo! All verified theorems/propositions/corollaries are linked to their corresponding Lean4 declarations in the table below. Note declaration names use `RankThreeProjection`.

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
