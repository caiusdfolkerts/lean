# A counterexample to Smilansky’s conjecture

This project formalises Caius Folkerts’s counterexample to cubical Minkowski decomposability: a full-dimensional rational four-polytope with 144 vertices, cubical facets, and no nontrivial Minkowski summand. It also proves the auxiliary 32-vertex block and the general redrawing criterion used in the paper.

## Verification

With Elan and Git installed, run these commands from this directory. The compiler and dependency revisions are pinned.

```sh
lake exe cache get
lake build
```

The default build checks the proof and the original three verification stages: declaration-wide axiom inspection, principal dependency analysis, and kernel-body replay. It permits only `propext`, `Classical.choice`, and `Quot.sound`. Downloading the dependency cache is not a proof check. The four assembled source modules are large; compilation may require substantial memory.


## Main results

Declaration names below use the namespace `CubicalIndecomposability` unless shown in full.

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
