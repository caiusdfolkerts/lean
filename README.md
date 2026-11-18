# Frozen Volume raw metadata diagnostic

Source is exactly `caiusdfolkerts/research` commit
`55fdfa7881012bf6d9662704616d90468c2d46f6`, project `volume_polynomials`.
No mathematical source or semantic data is changed by this diagnostic.

This reuses the tested immutable ellipsoid diagnostic setup and unmodified
Palomar verifier CLI pinned at `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`.
The same remote job retains the verifier's exports and runs the validated
Detailed helper, so it reports all reachable raw mismatch fields in one pass.
It is separate diagnostic evidence, not an official reusable preflight or
registry/intake authorization.

The helper distinguishes full type/universe equality, definition values,
reducibility hints for both exports, safety and mutual declaration metadata.
It traverses both sides after mismatches. Only bounded receipts/logs and the
exact mechanical report at audit time are retained. No export download occurs.

The combined export cap is explicitly1GiB, parser memory2GiB, audit300seconds,
and unmodified verifier execution budget19800seconds. The source's preceding
full run used export-phase disk peaks174MB/658MB and ComparatorRSS1.1GiB;
these measurements are not promises about the next execution.

Push branch trigger: `palomar-diagnostics/volume-raw`. The root worker owns
publication. This folder is a frozen publication bundle, not a git commit.

Preparation: Python/YAML syntax checked; Detailed helper previously passed
native-linked value-only and hint-only fixtures on the exact4.36rc1 toolchain.
No local Lean build, source edit or remote execution was performed here.
