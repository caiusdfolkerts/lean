# Quadratic generation for smooth polytopes with long edges

This project formalises the principal results of Caius Folkerts’s *Quadratic generation for smooth polytopes with long edges*. The source includes the supporting mathematics needed for the stated results.

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
| Theorem 1.1 | `ToricQuadratic.normal_and_quadratic` |
| Theorem 1.2, polytope form | `ToricQuadratic.prescribed_parity` |
| Theorem 1.2, divisor form | `ToricQuadratic.toric_paper_theorem_1_2` |
| Theorem 1.3, polytope form | `ToricQuadratic.adjoint_decomposition` |
| Theorem 1.3, divisor form | `ToricQuadratic.toric_paper_theorem_1_3` |
