# Dimension and identifiability of three-sunlet models

This project contains the full Lean4 formalisation for all principal results in my paper *Dimension and identifiability of three-sunlet models*.

## Verification

If you have Elan and Git installed, run below commands from this directory.

```sh
lake exe cache get
lake build
```

## Main results

Here's a guide to help you navigate this repo! All verified theorems/propositions/corollaries are linked to their corresponding Lean4 declarations in the table below.

| Paper result | Formal conclusion |
| --- | --- |
| Theorem 1.1 | Dimension 5m−4 for every normalized Latin system of order m≥5, in every characteristic; the original group model is identified explicitly. |
| Theorem 2.3 | Dimension 3m+2c−2 for the stated two transitive families of c nonidentity derangements. |
| Theorem 4.2 | Generic unordered toric decomposition, normalized degree 2c² (c is the order of the loop abelianization), the stated character-wreath Galois group, full general five-family fibers, and rationality over Q. |
| Corollary 5.1 | Degree two and precisely the two literal normalized parameter points for prime-order nonassociative loops. |
| Theorem 6.1 | The literal 8m−12 coordinates and a rational inverse to their projection over Q, for every m≥6. |
| Theorem 7.1 | The complete automorphism-orbit and inverse-stable-partition dimension classification, including both exceptional cases. |
| Corollary 7.4 | The cyclic orbit-model formula for every order n≥5 and every automorphism subgroup. |
| Corollary 8.1 | The complete dimension formula for actual finite binary level-one graphs, with triangles and the two-leaf edge case. |
