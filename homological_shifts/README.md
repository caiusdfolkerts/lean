# Rank formulas for homological shifts of polymatroidal ideals

[![Build](https://img.shields.io/github/actions/workflow/status/caiusdfolkerts/research/project-homological_shifts.yml?branch=main&label=&style=flat)](https://github.com/caiusdfolkerts/research/actions/workflows/project-homological_shifts.yml)

This project contains the full Lean4 formalisation for all principal results in my paper *Rank formulas for homological shifts of polymatroidal ideals*. I've included the paper as paper.pdf.

## Verification

If you have Elan and Git installed, run below commands from this directory.

```sh
lake exe cache get
lake build
```

## Main results

Here's a guide to help you navigate this repo! All verified theorems/propositions/corollaries are linked to their corresponding Lean4 declarations in the table below. Note declaration names use `FourPapers.Homological`.

| Paper result | Lean statement |
| --- | --- |
| Theorem 1.1, stabilization and generation | `theorem_1_1`, `theorem_1_1_twisted`, `theorem_1_1_generation` |
| Theorem 1.2, exact rank and canonicality | `theorem_1_2`, `theorem_1_2_canonical` |
| Corollary 4.1, mixed powers and generation | `corollary_4_1`, `corollary_4_1_generation` |
| Proposition 4.2, sharpness | `proposition_4_2` |
| Corollary 4.3, actual projective dimension | `corollary_4_3`, `corollary_4_3_eventual` |
| Theorem 4.4, exact generator interval | `theorem_4_4_zero`, `theorem_4_4`, `theorem_4_4_threshold_formula` |
| Theorem 5.1, total actual-Tor support | `theorem_5_1`, `theorem_5_1_rank`, `theorem_5_1_field_independent` |
| Theorem 6.1 and Corollary 6.2, integral closure | `theorem_6_1`, `corollary_6_2` |

## Independent Palomar interface

The current selection includes stabilization and fixed twists, exact and canonical rank, actual projective dimensions, ordinary-Rees generation, monic integral closure, field independence on every actual nonzero Koszul multidegree, and universal squarefree-Veronese sharpness in every positive degree. The interface uses the actual signed exterior differential and original chain submodules, with a genuine source iff to the retained homology definition.

The exact375-line interface and both differential/homology identity controls passed canonical run44463606794. The full source bridge, Comparator and kernel replay remain pending. This selection is not whole-paper coverage: mixed coordinate powers/Rees generation, exact generator intervals/thresholds, remaining total-support homogenized-ideal/rank clauses, and multi-Rees integral closure still require independent interfaces. See map.json for exact source and paper links.
