# Recovered differential and filtered development

These files preserve the 17 additional authored modules recovered from the
2 November checkpoint, with their complete historical import closure (27
authored modules and 11 TauCeti modules). The archive identity and recovery
record are documented in [recovery.md](../recovery.md).

This directory is outside the default Lake targets. The compiled publication
source is `../source/`; shared modules there include the completion repairs.
The historical copies here are not an alternative verified build.

| Development | Additional source modules |
| --- | --- |
| Divergence and homogeneous derivations | `PolynomialDivergence`, `PolynomialHomogeneousDerivations`, `DivergenceCocycleComplex` |
| Weighted pieces and affine comparison | `WeightedPolynomialPieces`, `DivergenceDegreeSpaces`, `DivergenceDegreeMatrices`, `AffineMatrixComplex`, `DivergenceAffineFamily`, `DivergenceDegreeQuotient` |
| Equivariant comparison of arbitrary relation spaces | `ProjectedComplexWithoutDomainAction`, `EquivariantComparisonFromArbitraryRelations` |
| Filtered module spanning and initial relations | `FermionFilteredModuleSpanning`, `FermionFilteredInitial` |
| Exactness and fixed complements | `FilteredComplexExactness`, `FilteredComplexNormalForms` |
| Quotient bases and normal representatives | `FilteredBasisTransfer`, `FilteredBasisNormalForm` |

The hash/import inventory is [historical-manifest.json](historical-manifest.json).
All local imports in the preserved historical closure resolve here, and its
external import headers were checked against the pinned dependency sources.
That is a source-availability check. The manifest distinguishes source
candidates from historical accepted compilation evidence.

The filtered lemmas establish finite descent and preservation of a specified
complement under explicit leading-map and complex hypotheses. The scalar
divergence work constructs the first two corrected maps. The final scope note
in the [project README](../README.md) specifies the remaining paper applications.
