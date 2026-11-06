# Gröbner bases for symmetric rank conditions

This project contains the full Lean4 formalisation for all principal results in my paper *Gröbner bases for symmetric rank conditions*.

## Verification

If you have Elan and Git installed, run below commands from this directory.

```sh
lake exe cache get
lake build
```

## Main results

Here's a guide to help you navigate this repo! All verified theorems/propositions/corollaries are linked to their corresponding Lean4 declarations in the table below. Note declaration names use `FourPapers.Symmetric`.

| Paper result | Main formal result |
| --- | --- |
| Theorem 1.1 | `symmetric_rank_loci`: primeness, the prescribed initial ideal, and the actual rank-locus vanishing ideal |
| Theorem 1.2 | `compatible_rank_and_symbolic_conditions`, `compatible_initial_ideal`, and `integral_rank_and_symbolic_conditions` |
| Theorem 2.1 | `insertion_statistics`, including the bijection, content, northwest rank statistic, and every packing statistic |
| Proposition 4.1 | `northwest_groebner` for every symmetric nonnegative bound array |
| Lemma 5.2 | `PaperStatements.lemma_5_2_quotient_chart`, with `K(x)` coefficients and independent polynomial carriers |
| Corollary 5.3 | `Schur.corollary_5_3_schur_hilbert_series` and the ordinary rank-cutoff specialization |
| Corollaries 6.1 and 6.3; Lemma 6.2 | Integral standard monomial bases, domains, geometric fibers, a simultaneous triangular basis, and compatible ideal lattices |
| Proposition 6.4 | `Deformation.latticeDeformation_standard_basis`, the free flat family, its fibers, and coefficient changes |
| Proposition 6.5 | `Strata.SymmetricRook.openSchemeIso`, `Strata.proposition_6_5_geometry`, and `Strata.proposition_6_5_scheme_point_count` |
| Corollary 7.1 | `Rees.corollary_7_1_sagbi` and `Rees.corollary_7_1_monomialBasis` |
| Corollary 7.2 | `IntegralClosure.corollary_7_2_first_part`, the full symbolic-power formula, and its integral models and compatible degenerations |
| Proposition 7.3 | `JointSagbi.proposition_7_3_sagbi`, including determinant cancellation and the smaller generating collection |
| Proposition 7.4 | `JointSagbi.not_isSagbiBasis_two_threshold` for every `t ≥ 4` and `n ≥ t + 1` |
| Sharp boundary | `JointSagbi.joint_minor_sagbi_iff_full_size`: for `4 ≤ t ≤ n`, the proposed collection is SAGBI precisely when `n = t` |
