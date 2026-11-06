# A counterexample to Smilansky’s conjecture

This project contains the full Lean4 formalisation for all principal results in my paper *A counterexample to Smilansky’s conjecture*.

## Verification

If you have Elan and Git installed, run below commands from this directory.

```sh
lake exe cache get
lake build
```

## Main results

Here's a guide to help you navigate this repo! All verified theorems/propositions/corollaries are linked to their corresponding Lean4 declarations in the table below. Note declaration names use `CubicalIndecomposability`.

| Paper result | Lean statement |
| --- | --- |
| Theorem 1: the rational, full-dimensional cubical and indecomposable witness | `theorem_one` |
| The exact face vector (144, 404, 390, 130) | `face_vector` |
| All parallel redrawings are homothetic | `parallel_redrawings_homothetic` |
| Arbitrary convex Minkowski summands are homothetic | `minkowski_summands` |
| Lemma 2: the literal one-dimensional deformation-space criterion | `lemma_two` |
| Lemma 3(i) | `lemma_three_one` |
| Lemma 3(ii) | `Papers.Polytopes.redrawing_zero_of_two_neighbors` |
| Proposition 5: the full auxiliary block statement | `Block.proposition_five` |
