# Explicit nonpolytopal Bier spheres

This project formalises the principal results of Caius Folkerts’s *Explicit nonpolytopal Bier spheres*. The source includes the supporting mathematics needed for the stated results.

## Verification

With Elan and Git installed, run these commands from this directory. The toolchain and dependency revisions are pinned in the supplied configuration.

```sh
lake exe cache get
lake build
```

The default build includes the mathematical source and checks that the imported project theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. Downloading the library cache is not itself a proof check.

## Main results

Unless otherwise qualified, declaration names use the namespace `Bier`.

| Paper result | Lean statement |
| --- | --- |
| Theorem 1, principal example | `principal_example` |
| Theorem 1 and §4.1, removing the ghost | `all_labels_example` |
| Theorem 1 and §4.2, self-dual input | `self_dual_example` |
| Theorem 1 and §4.3, input dimension three | `three_dimensional_example` |
| Theorem 2, fixed positive face cardinality | `ghost_signRank_bound_fixedCard` |
| Theorem 2, arbitrary face cardinalities | `ghost_signRank_bound_arbitrary` |
| Lemma 3 | `exists_core_schur_realization` |
| Lemma 4 | `paddedPrincipalInverse_span_finrank` |
| Forster [2, Theorem 2.2] | `Forster.signRank_spectral` |
| Hadamard column restriction | `Forster.hadamard_columnRestriction_signRank` |
| Bier sphere theorem [1] | `Complex.bier_isSphere` |
| Exact all-sign matrix rank | `allColumnSigns_signRank` |
| Final paragraph of §4.3 | `general_allSign_construction_unrestricted` |
