# Undecidability of mixed-volume realization

This project contains the full Lean4 formalisation for all principal results in my paper *Undecidability of mixed-volume realization*.

## Verification

If you have Elan and Git installed, run below commands from this directory.

```sh
lake exe cache get
lake build
```

## Main results

Here's a guide to help you navigate this repo! All verified theorems/propositions/corollaries are linked to their corresponding Lean4 declarations in the table below.

| Paper result | Lean statement |
| --- | --- |
| Theorem 1.1 | `MixedVolume.MainResults.theorem_1_1` |
| Point padding | `MixedVolume.MainResults.theorem_1_1_all_n` |
| Theorem 4.3 | `MixedVolume.MainResults.theorem_4_3` |
| Corollary 5.1 | `MixedVolume.FixedSection.corollary_5_1_exists` |
| Theorem 6.1 | `MixedVolume.ScalarSection.theorem_6_1` |
| Point padding in Section 6 | `MixedVolume.ScalarSection.theorem_6_1_all_n` |
| The literal Section 6 example | `MixedVolume.ThreeStateSection.theorem_6_1_literal_section` |
