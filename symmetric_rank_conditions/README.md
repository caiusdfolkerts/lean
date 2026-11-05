# Gröbner bases for symmetric rank conditions

This project formalises the principal results of Caius Folkerts’s *Gröbner bases for symmetric rank conditions*. The source includes the supporting mathematics needed for the stated results.

## Verification

With Elan and Git installed, run these commands from this directory. The toolchain and dependency revisions are pinned in the supplied configuration.

```sh
lake exe cache get
lake build
```

The default build includes the mathematical source and checks that the imported project theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. Downloading the library cache is not itself a proof check.

## Main results

Unless otherwise qualified, declaration names use the namespace `FourPapers.Symmetric`.

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
