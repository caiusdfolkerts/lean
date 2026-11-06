# Recovery and completion record

This project began with a substantial collection of Wishart source, checkpoints, repair fragments, and partial build evidence. The task was to determine exactly what was present, recover the strongest preserved proofs, close the remaining paper coverage, and obtain a fresh whole-project verification before publication.

The [recovered file index](verification/recovery-index.md) accounts for every original working-directory file. [The machine-readable inventory](verification/recovery-inventory.json) records byte sizes, SHA-256 hashes, origin mappings, local imports, and the static source scan. The separate [checkpoint inventory](verification/checkpoint-inventory.json) accounts for the contents of the two preserved checkpoint archives. These are provenance records; successful proof checking is established by a build receipt.

## What was already written

The initial source archive, `source-config-round1.tar.gz`, contained 265 Lean files and three configuration files. Its 120,764 lines included 215 vendored TauCeti support modules, the assembled Wishart modules, a public entry point, and an earlier verification file. The archive’s SHA-256 is `225c9e8d3fd896ab5dbbffab29b630cd68343fb7613105685e08bbccd10446e6`.

The surrounding directory contained 526 original files. Of the loose mathematical modules, 423 were already represented by `Source:` markers in the initial assembly. Five additional topic modules were genuine coverage additions, while the other twelve unmapped names were predecessor APIs or import-only wrappers. The final source index maps 428 original topic names to the assembled source. Sixty-five further Lean files were probes, baselines, or partial work variants; their existence did not make them additional completed mathematical targets.

The initial static scan found no proof holes, custom axioms, unsafe or partial mathematical definitions, native decision shortcuts, or kernel-checking bypass options. It found no missing local imports or import cycles. This was useful evidence about the source, but it did not show that the source compiled.

## What the checkpoints did and did not establish

| Recovered evidence | What it established | What remained open |
| --- | --- | --- |
| Initial assembled source archive | A complete-looking source tree and pinned configuration | Fresh compilation and comparison with the later repairs |
| `wishart_checkpoint_20261102_0951.zip` | A preserved development snapshot with 1,143 files and explicit checkpoint status | Later real modules, beta-II/field work, and full verification were unfinished |
| `wishart_checkpoint_20261102_1059.zip` | A later snapshot with 1,421 files, stronger statements, exact statement gates, and a proposed 101-endpoint audit | The checkpoint explicitly did not certify a completed full build or kernel replay |
| Later fragments and repair diffs | Specific improved proof sections and evidence of successful sub-builds | Reconstruction and fresh checking of the assembled final bytes |
| Historical command transcripts | Some individual target outcomes and the sequence of repair attempts | They did not establish successful checking of the complete Wishart project |

The highlighted 09:51 checkpoint inside the working directory was byte-identical to the already recovered copy: SHA-256 `f065f2c266b05adb3a96ec6af7ed873a0b9b853868e551ac94b91f9dc0485308`. A historical `AUDIT_COMPLETE: 858` line belonged to the separate StressFlex project and was not counted as Wishart evidence. Proposed audit commands and endpoint lists were likewise kept distinct from successful execution.

## Recovered and completed work

The later snapshots and saved fragments supplied explicit matrix-coercion, scalar-instance, measurability, finite-index and integration repairs. Where a complete later file was unavailable, preserved sections were matched against the archive and reconstructed before fresh compilation. The [repair ledger](verification/recovery-patches.json) records 71 historical transitions, their source hashes, and the origin of recovered changes; the [current-source record](verification/recovery-current-sources.json) separately identifies the final bytes after later compiler repairs. Compiler-driven repairs are applied to proofs while retaining the intended mathematical statements.

Five genuine omissions from the initial assembly were restored:

| Original topic | Contribution | Source location |
| --- | --- | --- |
| `SectionFiveEmptyBlocks.lean` | Determinant-one and constant-factor lemmas; Section 5 principal-block comparisons allowing empty determinant blocks | [real_clauses01](source/wishart/verified/real_clauses01.lean) |
| `SpectralProfileClosure.lean` | Product, nonnegative-sum and outer-composition profile rules, including singular boundary values | [spectral_profile_closure](source/wishart/verified/spectral_profile_closure.lean) |
| `SpectralExampleMoments.lean` | Polynomial evaluation, product moments and symmetric-norm envelopes | [spectral_example_moments](source/wishart/verified/spectral_example_moments.lean) |
| `FieldSpectralMoments.lean` | Actual-law probability, trace moments and normalized-compression eigenvalue moments | [field_spectral_moments](source/wishart/verified/field_spectral_moments.lean) |
| `FieldExampleFiniteMoments.lean` | Individual and joint finite moments for the final polynomial, trace and norm examples | [field_example_finite_moments](source/wishart/verified/field_example_finite_moments.lean) |

The paper’s explicit negative-covariance overlap example had no recovered actual-law proof. [overlap_obstruction](source/wishart/verified/overlap_obstruction.lean) adds the Bartlett-coordinate moments, transfer to the density-defined Wishart law, and the covariance calculation and negative witnesses. The final acceptance selection extends the historical 101 endpoints to cover this calculation and the restored closure and moment claims.

A later review of the hypotheses of the numbered supporting lemmas found two further mathematical gaps. The earlier radial infrastructure assumed `HasTemperateGrowth`, which includes global smoothness and bounds for every derivative. That did not prove Lemma 3.1 for an arbitrary function that is only $C^2$ near the cone with polynomial bounds on its value and first two derivatives. The new finite-order development extends local tests without changing their derivatives on the cone, establishes support-restricted Stein identities and differentiation under the integral, and transports the scalar real-shape equation through reduced covariance factors. Covariance regularization handles every positive semidefinite covariance in the integer case. The [real](source/wishart/verified/lemma_3_1_real.lean) and [integer](source/wishart/verified/lemma_3_1_integer.lean) endpoints and their [literal statement gates](source/verification/statements_radial_c2.lean) passed fresh module builds. The conclusions include the finite derivative at zero, ordinary derivatives in the ODE, integrability, and monotonicity under nonnegativity of the expected operator.

Lemma 7.2 had a different gap. The recovered positive-logarithm and spectral-specialization arguments did not establish its full class of continuous nonnegative factors whose logarithms may equal $-\infty$. The new [extended logarithmic submean proof](source/wishart/verified/extended_log_submean.lean) encodes zero values with an infinite nonnegative logarithmic defect, derives positive truncations, and passes finite products to the limit. The [actual Gaussian row argument](source/wishart/verified/field_row_logsubharmonic.lean) then proves integrability and monotonicity over both fields, including arbitrary rectangular covariance factors, compressions, offsets, and zero factors. This module and its [literal gates](source/verification/statements_row_logsubharmonic.lean) also passed fresh builds. The transitive axiom checks for the new radial and row-lemma endpoints use only `propext`, `Classical.choice`, and `Quot.sound`.

The partition lemma also needed an explicit endpoint at exactly the printed shape range. For proper blocks, $N>m$ implies the dimension bound used by the radial generator. For a single full block, that route would incorrectly demand $N\ge m+1$. The new [Lemma 3.3 endpoint](source/wishart/verified/lemma_3_3.lean) uses the one-determinant Gaussian comparison for this case, preserving $m<N<m+1$ and the stated strict comparison. Its [literal gates](source/verification/statements_radial_partition.lean) display the partition, determinant powers, and independent Wishart/Gaussian measure.

These are proofs of the printed hypotheses. Their successful sub-builds remain distinct from the final whole-project verification receipt.

The twelve loose names that remain outside the assembled origin map are accounted for rather than silently discarded. `AssociationTheory.lean` is a monolithic predecessor whose 184 declarations already occur in the core. `CompressionPowerProducts.lean`, `FieldLeadingBoundary.lean`, and `LogSpectralPartition.lean` contain earlier or intermediate interfaces superseded by more general conclusions in the assembly. The eight `Candidate`/`Verified` wrappers contain imports rather than new mathematics. Their individual dispositions are in the recovered file index.

## Manuscript and statement review

The entire current 25-page paper was compared with the explicit main endpoints, the literal statement gates, the unmapped source modules, and the final examples. This review led to the extra overlap, closure, and example-moment work, and the later exact-hypothesis review led to the full finite-order radial and extended-logarithm lemmas. Limiting acceptance to the old endpoint checklist would have missed those claims.

Two manuscript corrections were required. Page 14’s Anderson argument now compares opposite sections directly instead of asserting concavity across empty sections. The exact inverse-Wishart and beta-II positive-moment threshold on pages 18 and 20 now sums exponents only over positive-rank compressions. A zero-column determinant is one and has every moment. The [correction record](verification/manuscript-corrections.json) identifies the exact input/output hashes and replacement text. The three changed pages were rendered and inspected; all other pages were pixel-identical at the recorded comparison resolution.

## Reproducibility and provenance

The project pins Lean `4.36.0-rc1` and Mathlib revision `2cabef97b63d3275776b8b060d802de6a6fa1055`. All nine external package revisions are specified in `lake-manifest.json`. The 215 vendored TauCeti files were compared with the preserved vendor metadata: their source content is retained, with import spelling normalized for the assembled module layout. [The vendor provenance record](verification/vendored-support-provenance.json) records the comparison and the historically recorded upstream revision.

The local verification environment used official Lean binaries. Its restricted process filesystem required a narrow executable-location compatibility shim: when the runtime requested the known path to its own executable, the shim supplied the configured official installation path. It changed no compiler, proof kernel, elaborator, source dependency, or theorem check. Ordinary reader environments do not need this compatibility measure. The verification receipt records whether a runtime preload was present, and the environment record explains its scope.

The final verification contract is the ordinary pinned source build plus the complete declaration and endpoint audit described in [the theorem correspondence](verification/theorem-scope.md#what-the-build-checks). No claim of an independent alternative-kernel replay is made. A source manifest or successful sub-build is not substituted for the complete build result.

## Final verification

The full frozen project passed `python3 verification/verify.py` on 6 November 2026. The ordinary `lake build` completed 7,703 jobs with exit status zero. The fresh audit checked 11,161 declarations and 9,589 theorems across 298 imported local modules, including the vendored support, and accepted all 175 selected endpoints. It traversed 24,488 selected dependencies and admitted only `propext`, `Classical.choice`, and `Quot.sound`. Every selected exact theorem type passed serialization, decoding, and structural comparison. Source, configuration, manuscript, and all nine pinned dependencies remained unchanged during the run.

The [publication receipt](verification/build-result.json) binds this result to the exact input hashes. The full receipt, dependency/type report, and build log are preserved as compressed artifacts. The [final inventory](verification/recovery-inventory.json) contains 299 Lean source files and 130,307 lines; the extra module is the audit itself. No numbered assertion or stated example remains marked unfinished.

## Reader-facing package

The project follows the surrounding repository’s structure: a concise README, the paper, a theorem correspondence guide in the README, pinned Lake configuration, one authoritative source tree, and a verification directory. The historical files are indexed rather than copied into the reader’s main path. Original topic names remain in source comments and in the [source index](verification/source-index.md). Build products and diagnostic logs are generated under `.lake/`, outside version control.
