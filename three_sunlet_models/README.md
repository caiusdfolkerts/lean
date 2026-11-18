# Dimension and identifiability of three-sunlet models

[![Build](https://img.shields.io/github/actions/workflow/status/caiusdfolkerts/research/project-three_sunlet_models.yml?branch=main&label=&style=flat)](https://github.com/caiusdfolkerts/research/actions/workflows/project-three_sunlet_models.yml)

This project contains the full Lean4 formalisation for all principal results in my paper *Dimension and identifiability of three-sunlet models*. I've included the paper as paper.pdf.

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

## Palomar statement of record

The independent `Challenge.lean` selects every main theorem and substantive
corollary listed above, including the original group-coordinate dimension
statement, the exact normalized degree and character-wreath Galois equivalence,
full algebraic general fibers, rationality over the original characteristic-zero
field, literal two-point prime-loop ambiguity, all retained cyclic coordinates,
and both network formulas on actual binary level-one graphs.

The exact sixteen theorem declarations and one multiplicative-equivalence
definition are listed in `comparator.json`, alongside seven supporting theorem
obligations. `Solution.lean` imports their
substantive source implementations under the original names. All custom
polynomial maps, affine closures, normalized function fields, loop data,
partitions and graph definitions are inlined in the statement. Supporting
tangent/contact and field-reconstruction lemmas remain in the proof closure.

The independent Challenge passed its pinned remote elaboration check with the
23 intended theorem placeholders and the selected constructive Galois-value
placeholder. This checks the statement interfaces only. Full substantive
Solution compilation, strict Comparator and independent kernel verification
remain pending; the package is ready for that full preflight.
