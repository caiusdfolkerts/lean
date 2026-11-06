# Quadratic generation for smooth polytopes with long edges

This project contains the full Lean4 formalisation for all principal results in my paper *Quadratic generation for smooth polytopes with long edges*.

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
| Theorem 1.1 | `ToricQuadratic.normal_and_quadratic` |
| Theorem 1.2, polytope form | `ToricQuadratic.prescribed_parity` |
| Theorem 1.2, divisor form | `ToricQuadratic.toric_paper_theorem_1_2` |
| Theorem 1.3, polytope form | `ToricQuadratic.adjoint_decomposition` |
| Theorem 1.3, divisor form | `ToricQuadratic.toric_paper_theorem_1_3` |
