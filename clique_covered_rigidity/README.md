# Six-connected K4-covered graphs are rigid in three dimensions

[![Build](https://img.shields.io/github/actions/workflow/status/caiusdfolkerts/research/project-clique_covered_rigidity.yml?branch=main&label=&style=flat)](https://github.com/caiusdfolkerts/research/actions/workflows/project-clique_covered_rigidity.yml)

This project contains the full Lean4 formalisation for all principal results in my paper *Six-connected K4-covered graphs are rigid in three dimensions*. I've included the paper as paper.pdf.

## Verification

If you have Elan and Git installed, run below commands from this directory.

```sh
lake exe cache get
lake build
```

## Main results

Here's a guide to help you navigate this repo! All verified theorems/propositions/corollaries are linked to their corresponding Lean4 declarations in the table below. Note declaration names use `Papers.Rigidity`.

| Paper result | Lean statement |
| --- | --- |
| Theorem 1.1 | `sixConnected_k4Covered_rigid` |
| Corollary 1.2, edge cover | `sixConnected_rigidSubgraphCovered_rigid` |
| Corollary 1.2, completion | `rigidCluster_completion_sixConnected_rigid` |
| Theorem 5.1, all three clauses | `PairPinGraph.defect_theorem_at_algebraicallyGeneric_pins` |
| Theorem 5.1, maximum-rank form | `PairPinGraph.defect_at_maximal_rank_pins` |
| Sharpness of six-connectivity | `fiveConnected_k4Covered_flexible_exists` |
| Lemma 2.1, literal uniform priorities | `SupportedCode.uniform_priority_expectation_le_bound` |
| Lemma 2.1, equality examples | `SupportedCode.exists_code_attaining_uniform_priority_bound` |

## Palomar statement of record

`Challenge.lean` independently states Theorem 1.1, both parts of Corollary 1.2,
the five-connected sharpness assertion, and all three clauses of Theorem 5.1.
`Solution.lean` imports the substantive proofs, using their original names and
types. `comparator.json` lists precisely these five declarations.

The Challenge defines generic rigidity by the maximum rank of the actual real
bar-joint operator and compares it with the complete graph on the same vertex
set. A rigid cluster means that completing its vertex set adds no generic
rank to the ambient graph; its rigidity may pass through outside vertices.
The pair-pin quotient removes the common six-dimensional Euclidean twist
space from the actual compatibility kernel. Its defect is the maximum over
all partitions, with pair capacities 0, 3, 5, 6 for 0, 1, 2, at least 3 pins.
Algebraic independence is over Q for every actual pin occurrence coordinate.
The no-merged-bodies clause and simplicity clause retain their printed scope.

Three oversized proof modules have been split at balanced source-section
boundaries; the original module paths are public-import aggregators. No
mathematical statement or proof has been intentionally changed. The independent Challenge elaborates successfully against the unchanged
pinned Lean v4.35.0 and Mathlib, with only the selected theorem placeholders.
Full Solution compilation and Comparator remain pending.
