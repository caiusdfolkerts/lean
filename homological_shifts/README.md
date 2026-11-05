# Rank formulas for homological shifts of polymatroidal ideals

This project formalises the principal results of Caius Folkerts’s *Rank formulas for homological shifts of polymatroidal ideals*. The source includes the supporting mathematics needed for the stated results.

## Verification

With Elan and Git installed, run these commands from this directory. The toolchain and dependency revisions are pinned in the supplied configuration.

```sh
lake exe cache get
lake build
```

The default build includes the mathematical source and checks that the imported project theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. Downloading the library cache is not itself a proof check.

## Main results

Unless otherwise qualified, declaration names use the namespace `FourPapers.Homological`.

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
