# Frobenius generators for smooth toric varieties

This project contains the full Lean4 formalisation of the principal results in my paper *Frobenius generators for smooth toric varieties*.

## Verification

If you have Elan, Git and Python 3 installed, run these commands from this directory.

```sh
lake exe cache get
lake build
```

The project pins Lean 4.35.0 and its Mathlib revision. The build checks the sources and the axioms of the declarations below.

## Main results

All declarations below are in the `ToricPower` namespace, except where a longer namespace is shown.

| Paper result | Lean statement |
| --- | --- |
| Theorem 1.1: generation criterion for every Cartier divisor and all sufficiently large integer powers | `paper_theorem_1_1` |
| Proposition 3.2: complete-fan sufficiency | `toric_complete_cartier_eventual_generation` |
| Lemma 4.1, fan formulation: smooth completion preserving the original cones | `ToricPower.FanSubdivision.exists_complete_regular_extension_fullOnRays` |
| Theorem 5.2: the finite ray-span and integral-character criterion | `paper_theorem_5_2`, `paper_theorem_5_2_cartier` |
| Lemma 6.1: the universal grid and the full integral cokernel | `thomsenClasses_eq_frobenius_universal`, `thomsenClasses_eq_union_positive`, `paper_lemma_6_1_zonotope_grid` |
| Proposition 6.2: stabilization and the exact one-exponent generation test | `paper_proposition_6_2_classes_int`, `paper_proposition_6_2_DbCoh_invariant`, `paper_proposition_6_2_DbCoh_cartier` |
| Lemma 7.1: lattice absorption | `paper_lemma_7_1_int` |
| Theorem 7.2: raw-summand periodicity and generation at a height-linear bound | `paper_theorem_7_2`, `paper_theorem_7_2_cartier_generation`, `periodicityBound_eq_paper_formula` |

The accompanying [paper](paper.pdf) includes the corrected proof of Lemma 4.1, using a relative smooth refinement that preserves the original cones.
