# Volume polynomials and the Heine–Shephard problem

This project contains the full Lean4 formalisation for all principal results in my paper *Volume polynomials and the Heine–Shephard problem*.

## Verification

If you have Elan and Git installed, run below commands from this directory.

```sh
lake exe cache get
lake build
```

## Main results

Here's a guide to help you navigate this repo! All verified theorems/propositions/corollaries are linked to their corresponding Lean4 declarations in the table below. Note declaration names use `VolumePolynomials.Main`.

| Paper result | Lean statement |
| --- | --- |
| Theorem 1.1 | `semialgebraicity_iff` |
| Theorem 1.1, polytope clause | `polytope_locus_not_semialgebraic` |
| Theorem 1.2 | `shape_forcing` |
| Theorem 1.3, criterion | `countable_characterization` |
| Theorem 1.3, strict separation | `nonrealizable_strict_inequality` |
| Theorem 1.3, finite certificates | `finite_rational_certificate` |
| Theorem 1.3, rejection procedure | `rational_rejection_terminates` |
| Theorem 1.3, reconstruction | `rational_polytope_reconstruction` |
