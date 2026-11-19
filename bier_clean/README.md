# The first explicit nonpolytopal Bier spheres

[![Build](https://img.shields.io/github/actions/workflow/status/caiusdfolkerts/research/project-bier.yml?branch=main&label=&style=flat)](https://github.com/caiusdfolkerts/research/actions/workflows/project-bier.yml)

This project contains the full Lean4 formalisation for all principal results in my paper *The first explicit nonpolytopal Bier spheres*. I've included the paper as paper.pdf.

## Verification

If you have Elan and Git installed, run below commands from this directory.

```sh
lake exe cache get
lake build
```

## Main results

Here's a guide to help you navigate this repo! All verified theorems/propositions/corollaries are linked to their corresponding Lean4 declarations in the table below. Note declaration names use `Bier`.

| Paper result | Lean statement |
| --- | --- |
| Theorem 1, principal example | `principal_example` |
| Theorem 1 and §4.1, removing the ghost | `all_labels_example` |
| Theorem 1 and §4.2, self-dual input | `self_dual_example` |
| All-column-sign adaptation of §4.3, input dimension three | `three_dimensional_example` |
| Theorem 2, fixed positive face cardinality | `ghost_signRank_bound_fixedCard` |
| Theorem 2, arbitrary face cardinalities | `ghost_signRank_bound_arbitrary` |
| Lemma 3 | `exists_core_schur_realization` |
| Lemma 4 | `paddedPrincipalInverse_span_finrank` |
| Forster [2, Theorem 2.2] | `Forster.signRank_spectral` |
| Hadamard column restriction | `Forster.hadamard_columnRestriction_signRank` |
| Bier sphere theorem [1] | `Complex.bier_isSphere` |
| Exact all-sign matrix rank | `allColumnSigns_signRank` |
| Final paragraph of §4.3 | `general_allSign_construction_unrestricted` |

Provenance clarification: the selected input-dimension-three example has 2^73 anchors and sphere dimension 2^73+8; the manuscript uses binomial(75,37) anchors and dimension binomial(75,37)+8. The selected general family strengthens its threshold from m^2-m+3 to m^2-m+2. These proved adaptations retain the manuscript’s qualitative conclusions but are not identical quantitative constructions.
