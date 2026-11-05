# Undecidability of mixed-volume realization

This project formalises the principal results of Caius Folkerts’s *Undecidability of mixed-volume realization*. The source includes the supporting mathematics needed for the stated results.

## Verification

With Elan and Git installed, run these commands from this directory. The toolchain and dependency revisions are pinned in the supplied configuration.

```sh
lake exe cache get
lake build
```

The default build includes the mathematical source and checks that the imported project theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. Downloading the library cache is not itself a proof check.

## Main results

| Paper result | Lean statement |
| --- | --- |
| Theorem 1.1 | `MixedVolume.MainResults.theorem_1_1` |
| Point padding | `MixedVolume.MainResults.theorem_1_1_all_n` |
| Theorem 4.3 | `MixedVolume.MainResults.theorem_4_3` |
| Corollary 5.1 | `MixedVolume.FixedSection.corollary_5_1_exists` |
| Theorem 6.1 | `MixedVolume.ScalarSection.theorem_6_1` |
| Point padding in Section 6 | `MixedVolume.ScalarSection.theorem_6_1_all_n` |
| The literal Section 6 example | `MixedVolume.ThreeStateSection.theorem_6_1_literal_section` |
