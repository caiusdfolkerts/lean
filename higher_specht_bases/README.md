# Higher Specht bases for Springer and Δ-Springer rings

[![Build](https://img.shields.io/github/actions/workflow/status/caiusdfolkerts/research/project-higher_specht_bases.yml?branch=main&label=&style=flat)](https://github.com/caiusdfolkerts/research/actions/workflows/project-higher_specht_bases.yml)

This project contains the full Lean4 formalisation for all principal results in my paper *Higher Specht bases for Springer and Δ-Springer rings*. I've included the paper as paper.pdf.

The independent Comparator selection currently covers the prescribed Springer and Griffin bases, their exact field-characteristic ranges, and Corollary4.3 with every admissible dominance-triangular multiplier and arbitrary nonzero leading coefficient. Its521-line Challenge passed canonical elaboration; the current full Source/Solution/Comparator replay remains unverified. The required further principal results and corollaries are listed explicitly in map.json.

## Verification

If you have Elan and Git installed, run below commands from this directory.

```sh
lake exe cache get
lake build
```

## Main results

Here's a guide to help you navigate this repo! All verified theorems/propositions/corollaries are linked to their corresponding Lean4 declarations in the table below. Note declaration names use `HigherSpecht`.

| Paper result | Lean statement |
| --- | --- |
| **Theorem 1.1** | `springer_basis_target`, `theorem_1_1_basis` |
| **Theorem 3.2** | `theorem_3_2_selected_family`, `columnInsertion_state`, `columnInsertion_agrees_with_completed_run`, `columnInsertion_rearrangementWitness` |
| **Theorem 4.1** | `griffin_specifiedBasis`, `theorem_4_1`, `theorem_4_1_basis` |
| **Corollary 4.3** | `corollary_4_3_on_admissible_multipliers` |
| **Theorem 5.2** | `theorem_5_2`, `theorem_5_2_any_right_tableaux`, `theorem_5_2_actual_specht`, `theorem_5_2_literal`, `finiteCommonHarmonicVectorWithTableau_covariant`, `finiteCommonHarmonicCopyWithTableau_eq` |
| **Corollary 5.3** | `corollary_5_3_distributive`, `GriffinIdealExpression.corollary_5_3_basis`, `GriffinIdealExpression.corollary_5_3_frobenius` |
| **Corollary 5.5** | `corollary_5_5_decomposition`, `corollary_5_5_master`, `corollary_5_5_any_right_tableaux`, `corollary_5_5_actual_specht`, `griffinApolarWitness_full`, `griffinWitnessAlpha_full`, `griffinWitnessRejection_full`, `springerCommonHarmonicVector_literal_formula`, `springerCommonHarmonicVectorWithTableau_literal_formula`, `springerCommonHarmonicCopyWithTableau_eq` |
| **Corollary 5.6** | `corollary_5_6_basis`, `corollary_5_6_frobenius`, `finiteEligibility_weakDominanceJoin` |
| **Corollary 5.7** | `corollary_5_7_localized`, `corollary_5_7_field`, `adaptedGriffinCopy_eq_span` |
| **Theorem 6.1** | `theorem_6_1_basis_and_rank`, `theorem_6_1_dimension_and_cohenMacaulay`, `theorem_6_1_frobenius_series` |
| **Remark 6.2** | `untruncated_specified_parameter_basis_of_factorial_isUnit`, `remark_6_2_untruncated_characteristic`, `remark_6_2_untruncated_localized` |
| **Proposition 6.3** | `proposition_6_3`, `specialFiberPrescribedLiftBasis_apply`, `zeroParameterBaseChangeEquiv_one_tmul_mk` |
| **Corollary 6.5** | `untruncatedMonomialParameterBasis`, `corollary_6_5_allFields`, `griffinHilbertFunction_independent_field` |
| **Theorem 6.6** | `theorem_6_6`, `theorem_6_6_any_right_tableaux`, `theorem_6_6_actual_specht`, `theorem_6_6_literal`, `untruncatedCommonHarmonicVectorWithTableau_covariant`, `untruncatedCommonHarmonicCopyWithTableau_eq` |
| **Corollary 6.7** | `corollary_6_7_distributive`, `UntruncatedIdealExpression.corollary_6_7_basis`, `UntruncatedIdealExpression.corollary_6_7_frobenius`, `UntruncatedIdealExpression.corollary_6_7_parameters` |
| **Theorem 7.1** | `theorem_7_1_parameter_fiber`, `theorem_7_1_number_of_factors`, `theorem_7_1_after_scalar_extension`, `theorem_7_1_algebraicClosure` |
| **Proposition 7.2** | `proposition_7_2_integral_trivialization`, `proposition_7_2_integral_trivialization_coordinate`, `proposition_7_2_integral_trivialization_permutation`, `proposition_7_2_integral_induced_tensor`, `proposition_7_2_after_field_baseChange` |
| **Proposition 7.3** | `proposition_7_3_primary_decomposition`, `proposition_7_3_generic_component_length`, `proposition_7_3_multiplicities` |
| **Corollary 7.4** | `parameterFiber_geometricallyReduced_iff_polynomial`, `parameterPolynomial_separable_iff_geometric_squarefree`, `parameter_etale_atPrime_iff_polynomial` |
| **Corollary 7.5** | `regularity_statement` |
| **Corollary 7.6** | `springer_socle_concentrated_and_type`, `corollary_7_6_canonical_module`, `corollary_7_6_gorenstein_iff`, `corollary_7_6_completeIntersection_iff` |
| **Corollary 8.1** | `corollary_8_1_griffin_characteristic_all_partitions`, `corollary_8_1_springer_characteristic`, `corollary_8_1_griffin_copy_irreducible`, `corollary_8_1_springer_copy_irreducible`, `corollary_8_1_griffin_localized`, `corollary_8_1_springer_localized` |

Measured source proof repair after full run44391461523: the complete report contains two errors in the row/column subgroup-def proofs. Each subgroup is a literal abbreviation for its displayed fiber subgroup, so both equalities now use reflexivity. All statement types, mathematical definitions, guards, source licenses and the full five-target substantive scope remain unchanged. Full source/Solution/Comparator verification remains pending.
