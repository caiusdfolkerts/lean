# Source recovery and verification record

This note records the recovered Lean development and its preparation for this package. The mathematical account and theorem correspondence are in [formalisation.md](formalisation.md) and [README.md](README.md). The source under `source/` is the development used by the default build.

## The recovered checkpoint

The principal source checkpoint is `paper_verification_checkpoint.zip`, saved on 2 November 2026. Its SHA-256 is:

```text
3edcacd20ffd2f43d7f3aed219438ef934345a441e8abb0fcaf1124a0806f09f
```

The archive is 198,044,778 bytes and contains 7,231 entries. Much of its size is compiled support material. The recovery retained the mathematical source and the evidence needed to distinguish an accepted proof from a source candidate.

The first working selection contained 138 authored modules and 96 vendored TauCeti modules. Further inspection recovered 17 additional authored modules for differential operators, affine matrix comparison, and filtered normal forms. Their exact historical import closure comprises 27 authored modules and 11 TauCeti modules. The additional historical source is preserved under `reading/`; these copies are outside the default Lake targets. Shared modules in the compiled `source/` tree carry the subsequent repairs.

The inventory records source hashes and import relationships. It also records the differences between the recovered source and the publication source. This keeps the original work identifiable after proof repairs and the small reorganisation of the original-operator action module.

## What had already been checked

The archive contains an accepted build and axiom audit for Theorem 6.2, dated 1 November 2026. That check compiled `EulerJacobian` and `EulerParameters` from an empty project build directory and audited `PaperVerification.EulerJacobian.paper_theorem_6_2`. Its reported axioms were `propext`, `Classical.choice`, and `Quot.sound`.

The later isolated recovery had 81 successful module receipts: 18 authored modules and 63 TauCeti modules. All recorded source hashes matched the corresponding recovered files. The successful authored modules were:

- `EulerJacobian`, `EulerParameters`, and `EulerReduction`;
- `FermionMomentRecurrence`;
- `HomogeneousLocalization`, `HomogeneousNullstellensatz`, and `HomogeneousRegularSequence`;
- `MatrixRank`, `RankSpecialization`, and `SemisimpleHomComparison`;
- `PowerArtin`, `PowerArtinBasis`, `PowerBoundary`, `PowerConjugation`, `PowerHomogeneity`, `PowerOperators`, `PowerRecurrence`, and `PowerSpanning`.

The archive also contained complete statement candidates and proof scripts for Theorems 1.1 and 2.2. Those scripts already included the specified monomial bases, the full graded representation statements, and the sharp exceptional-parameter converse. The historical records did not contain a completed build certificate for their entire dependency closure. Completing that build, repairing its failures, and auditing the resulting endpoints were therefore necessary publication steps.

Three authored files had already been repaired after the archived checkpoint: `EulerParameters`, `PowerArtinBasis`, and `SemisimpleHomComparison`. Those changes were retained as the starting point. Thirteen support modules were also compared with their later published versions in the repository's two-fermion development. The comparison identified small proof-script changes in `HilbertTowerCount` and `FermionFiniteGrading`; it did not reveal a separate completed Hivert–Thiéry endpoint.

## Mathematical components recovered

| Component | Principal source families | Content |
| --- | --- | --- |
| Power operators and finite generation | `PowerOperators`, `PowerRecurrence`, `PowerComplex`, `PowerDegree*` | The actual operators, their recurrence and commutator identities, finite presentations of the infinite tails, and the deformed first two Koszul maps. |
| Literal monomial bases | `PowerFullSupport`, `PowerBoundary`, `PowerArtin*`, `PowerSpanning`, `PowerBasisTheorem` | The support filtration, coordinate reduction, upper and lower dimension bounds, and the specified Artin monomial classes. |
| Parameters and coefficient fields | `PowerParameters`, `PowerGenericParameters`, `PowerGroupedParameters`, `PowerStabilizerCharacteristic` | The paper's unbounded nonresonance condition, generic parameter fields, coefficient-preserving permutations, and the group-order consequence in positive characteristic. |
| Graded representation comparison | `EquivariantHom*`, `HomogeneousKoszul*`, `PowerRegularComparator`, `PowerGradedRepresentation`, `PowerRepresentationTheorem` | Equivariant rank comparison and reconstruction over the original field, followed by assembly across every homogeneous degree. |
| Original operator family | `PowerConjugation`, `PowerOriginalBasis`, `PowerOriginalAction`, `PowerOriginalRepresentation`, `PowerOriginalHilbert` | Actual diagonal conjugation, its equivariance and grading compatibility, and transfer of the basis, Hilbert series, and representation conclusions. |
| Sharp excluded parameters | `PowerHarmonic*`, `PowerFischerPairing`, `PowerStandard*`, `PowerResonantStandard`, `PowerCoinvariant*`, `PowerUniversalSlope`, `PowerExceptionalArtin` | Explicit harmonic witnesses, their quotient interpretation, comparison with ordinary coinvariants, and necessity of the exceptional-set exclusion. |
| Jacobian systems | `Euler*`, `Jacobian*`, `Hypersurface*`, `VectorEuler*`, `VectorJacobianKernel`, `CompleteIntersectionCodimensionFull` | Weighted Euler identities, reduction, parameter resonance, Brieskorn-module and defect constructions, and their equivariant counterparts. |
| Differential and filtered support | The additional modules indexed under `reading/` | Polynomial divergence, homogeneous derivations, scalar corrected maps, finite affine presentations, filtered exactness, and normal forms for a specified complement. |

The final row is recovered supporting work. The precise paper-level scope of the compiled package is the theorem table in the README; source names or conditional infrastructure theorems are not used as substitutes for completed applications.

## Completion changes

The completion build retained the mathematical statements and the paper's parameter hypotheses. Most changes made implicit coercions and coefficient maps explicit: a polynomial quotient can be viewed as a module in several ways, and an equality between those presentations must sometimes be supplied as a linear equivalence. Other repairs updated renamed library lemmas, made intertwining identities pointwise at the required vector, and prevented the elaborator from unfolding large quotient constructions while inferring arguments.

The source also uses explicit instances where unnamed instances from independently compiled modules would collide. A few proofs received larger local elaboration budgets. These are resource settings; kernel checking remains enabled. The original-operator action and diagonal-equivariance constructions were separated into `PowerOriginalAction`, allowing their finite-presentation and harmonic applications to compile independently of the final graded comparison theorem.

No paper theorem was replaced by a dimension-only statement, a calculation in a bounded degree range, or a result that assumes the desired equivalence. The endpoint correspondence is checked against the actual polynomial image quotients, monomial classes, homogeneous pieces, and permutation actions.

## Reproducible environment and audit

The package pins Lean `v4.36.0-rc1` and Mathlib revision `2cabef97b63d3275776b8b060d802de6a6fa1055`. The Lean compiler reports commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`. All nine external dependency checkouts used for the publication build matched their manifest revisions and had no tracked source changes. The required TauCeti source is vendored with its original headers and license; its recorded upstream revision is `06d5bb4e3ebb737dc6538567f5c53bf8800b9362`.

The default `lake build` includes both the mathematical libraries and `DeformedCoinvariants.KernelAudit`. The audit determines local ownership from module indices, reads the checked kernel environment, rejects project axioms and unapproved transitive axioms, and inspects the selected theorem dependency paths for unsafe or partial declarations. The permitted foundational axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.

The audit exports the selected theorem types as expression DAGs, decodes the JSON, and checks structural equality with the kernel types before writing its report. Its generated report is `.lake/reports/audit/kernel-dependencies.json`. The report distinguishes dependency bodies available to the audit from imported library declarations for which the environment supplies axiom summaries. This audit accompanies the source build; it does not turn a cached artifact or an uncompiled source file into a verified theorem.

The build configuration, mathematical sources, theorem checks, and documentation are committed together. The source and recovery manifests provide the corresponding hashes.

The separate [theorem correspondence review](verification/theorem-scope.md) checks each of the eight release endpoints against the manuscript, including the definitions, hypotheses, grading shifts, basis values, and group actions. This mathematical review complements the compiler and dependency audit.
