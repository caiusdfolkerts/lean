# Hilbert series of exterior algebras modulo two quadrics

This project formalises selected results of Caius Folkerts’s *Hilbert series of exterior algebras modulo two quadrics*. Theorems 1.1 and 1.3 and the specified algebraic results in Sections 5 and 7 are included.

## Verification

With Elan and Git installed, run these commands from this directory. The toolchain and dependency revisions are pinned in the supplied configuration.

```sh
lake exe cache get
lake build
```

The default build includes the mathematical source and checks that the imported project theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. Downloading the library cache is not itself a proof check.

## Main results

Unless otherwise qualified, declaration names use `PaperVerification.AlternatingForms`.

| Paper result | Lean statement |
| --- | --- |
| Theorem 1.1, pp. 1–2 | `paper_theorem_1_1`, `paper_theorem_1_1_hilbertSeries` |
| Theorem 1.1, combined reader-facing form | `PaperVerification.MainStatements.genericHilbertSeriesAndVanishing` |
| Theorem 1.3, combined statement | `paper_theorem_1_3_fully_graded` |
| Theorem 1.3, exterior basis, p. 3 | `paper_theorem_1_3_exterior_basis` |
| Theorem 1.3, algebraic and section-ring clauses | `paper_theorem_1_3`, `paper_theorem_1_3_complete_section_ring` |
| Proposition 5.1, p. 16 | `paper_proposition_5_1` |
| Corollary 5.2, p. 16 | `TopRepresentation.paper_corollary_5_2` |
| Proposition 5.3, p. 17 | `paper_proposition_5_3_koszul_classification` |
| Proposition 5.3, quadratic dual | `paper_proposition_5_3_dual_clause` |
| Proposition 5.4, pp. 17–18 | `paper_proposition_5_4`, `paper_proposition_5_4_origin`, `exteriorOriginBettiPolynomial_is_ordinary` |
| Lie-cohomology formulas after Proposition 5.4, p. 18 | `PaperVerification.TwoStepOriginalLieCohomology.paper_lie_cohomology_poincare`, `PaperVerification.TwoStepOriginalLieCohomology.paper_lie_cohomology_degree`, `PaperVerification.TwoStepOriginalLieCohomology.total_dimension_four` |
| Theorem 7.1, p. 20 | `paper_theorem_7_1_exterior_basis`, `paper_theorem_7_1_initial_ideal`, `paper_theorem_7_1_initial_ideal_one_plane`, `paper_theorem_7_1_full_hilbert` |
| Integral extension after Theorem 7.1, p. 20 | `IntegralOdd.paper_theorem_7_1_integral_full_basis`, `IntegralOdd.paper_theorem_7_1_integral_arbitrary_base_change`, `IntegralOdd.paper_theorem_7_1_integral_arbitrary_base_change_apply` |
| Theorem 7.2, pp. 20–21 | `paper_theorem_7_2` |

I’m still working on formalising the general geometric statement of Theorem 1.2, the ring identifications of Theorem 4.1, and the sheaf-cohomology assertions of Section 6. I plan to release these additions in the next few days.
