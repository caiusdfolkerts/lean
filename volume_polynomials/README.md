# Volume polynomials and the Heine–Shephard problem

This project formalises the principal results of Caius Folkerts’s *Volume polynomials and the Heine–Shephard problem*. The source includes the supporting mathematics needed for the stated results.

## Verification

With Elan and Git installed, run these commands from this directory. The toolchain and dependency revisions are pinned in the supplied configuration.

```sh
lake exe cache get
lake build
```

The default build includes the mathematical source and checks that the imported project theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. Downloading the library cache is not itself a proof check.

## Main results

Unless otherwise qualified, declaration names use the namespace `VolumePolynomials.Main`.

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
