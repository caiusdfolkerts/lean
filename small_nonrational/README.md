# Small nonrational four-polytopes

This project formalises the principal results of Caius Folkerts’s *Small nonrational four-polytopes*: a nonrational four-polytope on seventeen vertices, rational realizability of every four-polytope on at most ten vertices, and the deletion, density and classification results connecting them. The statements concern actual convex polytopes and their complete face lattices. In particular, the minimum possible number of vertices of a nonrational four-polytope lies between eleven and seventeen.

## Verification

With Lean installed through elan, Git, and Python 3.11 or later, run this command from this directory:

```sh
lake build
```

The pinned configuration selects Lean 4.35.0 and its matching Mathlib revision. The command fetches the required library cache, compiles every project source, and checks the principal statements and the axiom dependencies of all original proof occurrences. This is a substantial computation: the complete release was checked on a 16-core Linux machine with 64 GB of RAM. Keep at least 64 GB of working disk space available. Successful compilation steps are retained, so the same command resumes an interrupted build. Generated files stay in `.lake/`.

## Main results

The principal statements are assembled in `source/papers/small_nonrational.lean`, in the namespace `Papers.SmallNonrational`.

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

The formalisation includes the rational witnesses and obstruction proofs needed by the terminal classification, and three additional Appendix B density results. It does not claim every unnumbered local parametrisation in Appendix B. `formalisation.md` explains the mathematics and the source organisation.
