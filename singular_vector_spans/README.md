# Singular-vector spans beyond boundary format

This project contains the full Lean4 formalisation for all principal results in my paper *Singular-vector spans beyond boundary format*.

## Verification

If you have Elan and Git installed, run below commands from this directory.

```sh
lake exe cache get
lake build
```

## Main results

Here's a guide to help you navigate this repo! All verified theorems/propositions/corollaries are linked to their corresponding Lean4 declarations in the table below. Note declaration names use `PaperVerification.Segre`.

| Paper | Principal Lean declaration | Mathematical content |
|---|---|---|
| Theorem 1.1 | `SymmetricPrincipal.theorem_1_1_symmetric_rank` | Maximal rank and the exact exceptional kernel dimension for the first multiplication map in the actual symmetric-power Segre quotient. Every positive tuple and every characteristic are included. |
| Theorem 1.1, nonemptiness | `SymmetricPrincipal.theorem_1_1_symmetric_nonempty` | Existence of parameters and a degree-one quotient element satisfying the full conclusion. |
| Theorem 1.1, one factor | `SymmetricPrincipal.theorem_1_1_symmetric_one_factor` | The entire general reduction is algebra-isomorphic to the field. |
| Theorem 1.1, a projective-line factor | `SymmetricPrincipal.theorem_1_1_symmetric_projective_line` | The actual degree-two quotient piece is zero for the two-factor family with one projective dimension equal to one. |
| Proposition 2.1 | `EmbeddedSchemePrincipal.proposition_2_1` | The graph-span intersection, its dimension, and membership of the original tensor, with the printed hypotheses on the actual embedded singular scheme. |
| Lemma 2.2 | `EmbeddedSchemePrincipal.lemma_2_2` | Generic finiteness and reducedness of the actual embedded singular-tuple scheme. |
| Lemma 2.2, graph range | `EmbeddedSchemePrincipal.lemma_2_2_graph` | A common nonempty coefficient open supplies base-point-freeness, finiteness, and reducedness. |
| Corollary 1.2 | `OriginalProjectivePrincipal.corollary_1_2` | The exact first-excess defect, using ordinary tensor products and projective spans, with factor permutations. |
| The projective-line family after Corollary 1.2 | `OriginalProjectivePrincipal.projective_line_family` | Defect `b` for format `(2, b+1, b+3)`. |
| The matrix case after Corollary 1.2 | `OriginalProjectivePrincipal.matrix_first_excess` | Zero defect in the matrix family. |
| Theorem 1.3 | `PrincipalTensor.theorem_1_3` | A generic tensor of every format belongs to the ordinary linear span of its singular pure tensors. Zero projective dimensions and the one-factor case are retained. |
| Theorem 1.3, explicit linear combination | `PrincipalTensor.theorem_1_3_finite_linear_combination` | The same generic open supplies finitely many actual singular tuples and scalars whose weighted pure-tensor sum is the original tensor. |
| Theorem 1.3, empty-format convention | `PrincipalTensor.theorem_1_3_all_arities` | Extends the ordinary nonempty-format theorem to every natural number of factors, including the scalar empty tensor product. |
| Proposition 5.1 | `RigidityPrincipal.proposition_5_1_rigid`, `RigidityPrincipal.proposition_5_1_stress_free` | The complete positive product-of-chains classification, including every permutation of the three exceptional triples, on nonempty opens of actual placements. |
| Theorem 6.1, first bound | `OriginalProjectivePrincipal.theorem_6_1_first` | Full generic span when `k ≥ 4e`. |
| Theorem 6.1, three-block bound | `OriginalProjectivePrincipal.theorem_6_1_second` | Full generic span when `b ≥ 4`, `k ≥ 3b`, and `e ≤ 2^b − 3b + 1`. |
| Theorem 6.1, logarithmic consequence | `OriginalProjectivePrincipal.theorem_6_1_logarithmic` | Full generic span when `e ≥ 3` and `k ≥ 3⌈log₂(4e)⌉`. |
| Theorem 6.3 | `OriginalProjectivePrincipal.theorem_6_3` | The complete diagonal-box criterion with its exact inequality and every coordinate at least the specified `N`. |
| Final explicit bounds, three smaller factors | `OriginalProjectivePrincipal.three_factor_sqrt_bound` | The exact threshold `nᵢ ≥ 2e + 2⌈√(7e)⌉`. |
| Final explicit bounds, a fixed number of smaller factors | `OriginalProjectivePrincipal.many_factor_root_bound` | The exact threshold `nᵢ ≥ e + 2⌈((k+1)e)^(1/⌈k/2⌉)⌉ + 4k − 2`, for `k ≥ 4`. |
| Final explicit bounds, uniform bound | `OriginalProjectivePrincipal.uniform_large_factors` | Full generic span when every `nᵢ ≥ 3e²`. |
| Final explicit bounds, excess two | `OriginalProjectivePrincipal.excess_two_six` | Full generic span at excess two when every smaller projective dimension is at least six. |
| Final explicit bounds, growth of the explicit bounds | `AsymptoticGrowth.three_factor_growth`, `AsymptoticGrowth.many_factor_growth` | Actual `Asymptotics.IsBigO` statements along natural excess tending to infinity: `2e + O(√e)` and, for fixed `k ≥ 4`, `e + Oₖ(e^(1/⌈k/2⌉))`. |
