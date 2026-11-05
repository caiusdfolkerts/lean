# Six-connected K4-covered graphs are rigid in three dimensions

This project formalises the principal results of Caius Folkerts’s *Six-connected K4-covered graphs are rigid in three dimensions*. The source includes the supporting mathematics needed for the stated results.

## Verification

With Elan and Git installed, run these commands from this directory. The toolchain and dependency revisions are pinned in the supplied configuration.

```sh
lake exe cache get
lake build
```

The default build includes the mathematical source and checks that the imported project theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. Downloading the library cache is not itself a proof check.

## Main results

Unless otherwise qualified, declaration names use the namespace `Papers.Rigidity`.

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
