# Verification environment

The package pins Lean `4.36.0-rc1` (compiler commit `c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`) and the nine dependency revisions in `lake-manifest.json`. Mathlib is pinned to `2cabef97b63d3275776b8b060d802de6a6fa1055`.

## Official toolchain

The Linux toolchain was installed through Elan from the [official Lean release](https://github.com/leanprover/lean4/releases/tag/v4.36.0-rc1). Its release asset metadata reports a 605,563,669-byte archive with SHA-256 `26b3cea1a006ad419215520b8668dcd3f6a9eeba1a123756563a739f9c6274b2`. Elan removed the downloaded archive after installation, so this archive digest is published release metadata, not a locally recomputed download hash.

The installed files were hashed locally:

| Installed component | SHA-256 |
| --- | --- |
| `bin/lean` | `db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00` |
| `lib/lean/libleanshared.so` | `593af26b21d188f3f256f03de4da380c1288816202eef941652200eaab265990` |

The compiler accepted a basic arithmetic proof and rejected an intentionally mismatched proof of `False`. These checks establish that the installed command works and rejects that malformed proof; the project’s actual proof evidence is the subsequent source build and declaration audit.

## Executable-location compatibility

This execution environment denies numbered process-filesystem paths. The official runtime calls `readlink` on `/proc/<its-own-pid>/exe` to find its installation and therefore initially stopped with `failed to locate application`.

The small [compatibility source](environment/procfs-path-compat.c) supplies the already known configured installation path for that one request. Every other `readlink` call is delegated to the original operating-system implementation. It does not read a denied path, change access permissions, modify Lean binaries or libraries, alter kernel checking, or provide theorem implementations. The resulting library was supplied through `LD_PRELOAD`; the publication receipt records its digest.

Ordinary reader environments do not require this shim. Follow the README’s Elan/Lake commands directly. The source is included solely to make the verification environment inspectable.

## Dependencies and resource settings

All nine dependency checkouts were fetched at the exact revisions recorded in the manifest. The verification runner checks those revisions and requires their tracked source to be clean before and after the build. Mathlib’s cache supplies compiled dependency artifacts; the local Wishart and TauCeti source is built separately.

Lake is configured with one Lean worker per module, synchronous elaboration, and kernel checking explicitly enabled. Diagnostic logs and regenerated reports live under `.lake/reports/`. Neither a downloaded cache nor an environment setup report is counted as successful project verification.
