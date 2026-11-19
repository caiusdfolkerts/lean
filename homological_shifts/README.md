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

The current629-line interface selects the full main-theorem and substantive-corollary conclusions listed above: actual Koszul/derived-Tor shifts, exact minimal-generator intervals and signed thresholds, the complete homogenized total-support ideal with genuine projective dimension and every actual Tor generator, and ordinary/multi-Rees generation and integral closure for arbitrary finite colors and fixed twists. Original variable sets and zero coordinates are retained.

The complete interface and seven constructor controls passed canonical run44471557578. Current full Source/Solution bridges, Comparator and independent kernel replay remain pending; the earlier375-line selection passed run44465541716. All historical proof modules and principal audits remain included. Exact source/paper mapping and validation status are in map.json.
