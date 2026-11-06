# Small nonrational four-polytopes

This project contains the full Lean4 formalisation for all principal results in my paper *Small nonrational four-polytopes*.

## Verification

If you have Elan and Git installed, run below commands from this directory.

```sh
lake exe cache get
lake build
```

## Main results

Here's a guide to help you navigate this repo! All verified theorems/propositions/corollaries are linked to their corresponding Lean4 declarations in the table below. Note declaration names use `Papers.SmallNonrational`.

| Paper result | Lean declaration | Conclusion |
| --- | --- | --- |
| Theorem 1 | `theoremOne` | A seventeen-vertex four-polytope realizable over a real subfield exactly when that field contains √5. |
| Theorem 2 | `theoremTwo` | Every four-polytope with at most ten vertices is rationally realizable. |
| Theorem 3 | `theoremThree` | Simple-vertex deletion preserves the intrinsic deleted type, realization fields and rational density, in every dimension under the paper’s hypotheses. |
| Corollary 4 | `corollaryFour` | Every eleven-vertex four-polytope with a simple vertex is rationally realizable. |
| Proposition 7 | `propositionSeven` | The incidence and height reconstruction criterion gives density of the whole combinatorial type. |
| Proposition 8 | `propositionEight_i`, `propositionEight_ii`, `propositionEight_iii` | The three density criteria, including the global conclusion from one realization admitting at most eight relation rows. |
| Proposition 9 | `propositionNine` | Every residual ten-vertex type satisfies the projection criterion or is an explicit Appendix B alternative. |
| Lemma 11 | `lemmaEleven` | The full rank-four rational-density classification, with its golden exception. |
| Lemma 12 | `lemmaTwelve` | Rational approximation of multiaffine zeros, including singular original zeros. |
| Vertex bounds | `seventeenVertexNonrational`, `nonrationalVertexLowerBound`, `vertexBounds`, `minimumVertexBounds` | Existence and attainment of the minimum, with 11 ≤ N ≤ 17. |
