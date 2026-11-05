# Sublattice resolutions and Betti preservation in all powers

This project formalises the principal results of Caius Folkerts’s *Sublattice resolutions and Betti preservation in all powers*, including the mixed, integral, determinantal, cellular, and characteristic-dependence extensions. The general auxiliary formulations of Proposition 2.5 and Lemmas 3.3 and 9.2 are replaced by direct arguments for their applications; Lemma 4.2 is proved in the sublattice setting used by Theorem 4.3.

## Verification

With Elan and Git installed, run these commands from this directory. The toolchain and dependency revisions are pinned in the supplied configuration.

```sh
lake exe cache get
lake build
```

The default build compiles all 227 mathematical modules and the original strict audit. The audit loads their complete kernel bodies, checks every project declaration and the 359 selected theorem and identification endpoints, and rejects project axioms, incomplete proofs, and unapproved transitive axioms. Unsafe or partial declarations cannot occur on a selected mathematical root’s dependency path. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. Its report is written to `.lake/reports/audit/kernel-dependencies.json`. Downloading the library cache is not itself a proof check.


## Main results

Unless otherwise qualified, declaration names use the namespace `FourPapers.Sublattice`.

| Paper result | Lean statement |
| --- | --- |
| Theorem 1.1, closed graphs in the original labelling | `theorem11_integer_bettiEquality` |
| Theorem 1.2, signed fine formula and Rees-homology generation | `theorem12` |
| Proposition 2.2, literal finite Rees presentation | `proposition22` |
| Proposition 3.1, multiplicative propagation | `proposition31` |
| Theorems 4.1 and 4.3, ideal identities and conditional Betti transfer | `RowCutNetwork.theorem41`, `theorem43`, `theorem43_integer_betti`, `theorem43_finer_betti_of_refines` |
| Corollaries 5.1–5.3, finite formulas and the multiplication-induced Tor injection | `corollary51_integer`, `corollary52_integer_grouped_expansion`, `corollary53_chosenMinimumGenerator_paperTor` |
| Theorem 5.5, mixed products and unit-colour generation | `theorem55_betti_of_individual_integer_premise`, `theorem55_literal_generation` |
| Corollaries 5.6–5.7, finite and nested initial criteria | `corollary56_initial`, `corollary56_betti`, `corollary57_ideal_identities` |
| Corollary 5.8, positive homogeneous regular substitution | `corollary58_powerFreeResolution` |
| Section 6, retained-ring recursion, graph gradings and determinant powers | `lemma61_quotientBetti_recursion_arbitrary_variables`, `corollary62_natural`, `corollary64_closed`, `theorem65_integer` |
| Theorem 7.1 and Corollary 7.2, integral and mixed comparisons | `theorem71_actualIntegral`, `theorem71_baseChange`, `theorem71_arbitraryWeightFamily`, `corollary72` |
| Theorem 8.1, cellular resolution and numerical invariants | `theorem81_cellularResolution`, `theorem81`, `theorem81_integer_support`, `theorem81_integer_regularity`, `theorem81_depth_integer` |
| Theorem 9.1, the integral graph family and arbitrary coefficient change | `theorem91`, `theorem91_same_ranks` |
| Proposition 10.2 and Corollary 10.3, torsion and finite-complex realization | `RP2.theorem102_integral`, `RP2.theorem102_betti`, `FiniteComplexIncidence.theorem103_all_degrees` |
| Corollary 10.4, characteristic excess and independence in all powers | `corollary104_integer_grouped_expansion`, `corollary104_integer_global_exists_iff_all_powers` |
