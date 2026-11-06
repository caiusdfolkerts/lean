# Six-connected K4-covered graphs are rigid in three dimensions

This project contains the full Lean4 formalisation for all principal results in my paper *Six-connected K4-covered graphs are rigid in three dimensions*.

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
