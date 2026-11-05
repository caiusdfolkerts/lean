# Upstream attribution for the audit utilities

This notice concerns the audit utilities and their adaptations of Lean's official replay/checker routines. It does not relicense the mathematical manuscript or unrelated project sources.

The theorem-duplicate criterion and use of `Lean.Kernel.Environment.replay` follow `src/Lean/Replay.lean` in Lean 4. The quotient-package handling follows the official `src/LeanChecker.lean`. Their upstream notices are retained here:

> Copyright (c) 2023 Kim Morrison. All rights reserved.
> Released under Apache 2.0 license as described in the file LICENSE.
> Authors: Kim Morrison (Replay); Kim Morrison, Sebastian Ullrich (LeanChecker).

The original module-data APIs are defined in `src/Lean/Environment.lean`:

> Copyright (c) 2019 Microsoft Corporation. All rights reserved.
> Released under Apache 2.0 license as described in the file LICENSE.
> Authors: Leonardo de Moura.

The Python inspection utilities follow the official LeanExport 3.1.0 serialized-expression format. The upstream exporter and parser (`src/LeanExport/Basic.lean` and `src/LeanExport/Parse.lean`) carry:

> Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
> Released under Apache 2.0 license as described in the file LICENSE.
> Authors: Henrik Böving.

The complete Apache License 2.0 text is included in `Lean-APACHE-2.0.txt`. Adaptations in `scripts/Full21DependencyGraph.lean` add explicit original-private import discovery, graph and provenance output, exact root and safety checks, and optional official empty-kernel replay. They do not modify Lean's kernel or the imported `Lean.Kernel.Environment.replay` implementation. The Python tools are supplementary data inspectors, not replacement proof checkers. This attribution accompanies the exact tested helper source; no comment or code edit was made after its successful run merely to change its source hash.

Pinned primary-source links:

- [Lean Replay](https://github.com/leanprover/lean4/blob/b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a/src/Lean/Replay.lean).
- [LeanChecker](https://github.com/leanprover/lean4/blob/b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a/src/LeanChecker.lean).
- [Environment/module-data APIs](https://github.com/leanprover/lean4/blob/b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a/src/Lean/Environment.lean).
- [Official Apache license](https://github.com/leanprover/lean4/blob/b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a/LICENSE).

`upstream-license-binding.json` records the retrieved pinned license and LeanChecker source hashes. `official-replay-source-comparison.json` records the identical reviewed Replay source across the two independently checked toolchain pins.
