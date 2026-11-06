# Hilbert series of exterior algebras modulo two quadrics

This project contains the full Lean4 formalisation to Theorems 1.1, 1.3 and most algebraic results in Sections 5 and 7 from my paper *Hilbert series of exterior algebras modulo two quadrics*. I’m still working on the formalisation of the general geometric statement of Theorem 1.2 and parts of Theorem 4.1, but I expect them to be ready in a few days.

## Verification

If you have Elan and Git installed, run below commands from this directory. 

```sh
lake exe cache get
lake build
```

## Guide

Here's a guide to help you navigate this repo! All verified theorems/propositions/corollaries are linked to their corresponding Lean4 declarations in the table below. Note declaration names use `PaperVerification.AlternatingForms`.

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
