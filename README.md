# Small nonrational four-polytopes, block 0528 diagnostic

The workflow compares two proofs of `Papers.RationalityTen.GraphFiniteDispatch.Blocks.GraphCompactBlock0528.complete`. The statement asserts resolution of every original compact route key with index at least 21816 and less than 21834. This is one finite input to the ten-vertex rationality theorem. The replacement uses all 18 original records and their typed vertex-permutation and terminal witnesses.

The original job checks the byte-identical upstream sources at `e0696fddcd3d10b5d6461e62e9b2f02c4195be37`. The replacement job checks an independently staged module tree with the same endpoint and global key table. Files shared byte for byte are stored once. Both jobs verify the source manifest, compile from empty build directories, force ordinary Lean kernel checking, and separately export the exact publicly named proof. Both exports include the same Lean 4.35 Comparator primitives. The workflow replays each with the toolchain's ordinary Lean kernel, NanoDa and verified con-ron. [Upstream project](https://github.com/caiusdfolkerts/research/tree/e0696fddcd3d10b5d6461e62e9b2f02c4195be37/small_nonrational)

Both closures import only Lean and Init outside the project. The original pinned Mathlib manifest is retained, and neither job downloads or builds Mathlib. Both use `leanprover/lean4:v4.35.0`. Three compiler processes can run at once. Each compiler has one worker, an allocator limit of 4,096 MiB, and kernel typechecking enabled. `diagnostic/manifest.json` records per-file source hashes and the original repository location of every upstream module.

A push to `palomar/diagnostic-small-nonrational-block0528` runs the two jobs on standard Ubuntu 24.04 hosted runners. Each bounded JSON report includes the commit, tool hashes, compiler-phase timing, peak process RSS, export bytes and SHA-256, exported declaration count, reported axioms and each replay's exit status. A failed phase records a diagnostic tail of up to 12,000 bytes. Build outputs and exports stay on the ephemeral runner. Results describe this single block. This workflow is an ordinary diagnostic build. The complete lower-bound solution still requires a full Palomar preflight.

To validate the manifest and exact import closures offline, run these commands at the checkout root with Python 3.11 or later.

```sh
python3 diagnostic/run.py replacement
python3 diagnostic/run.py original
```
