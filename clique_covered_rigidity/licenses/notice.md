# Source provenance and attribution

This project formalises the supplied manuscript by Caius Folkerts,
*Six-connected K4-covered graphs are rigid in three dimensions*.
The manuscript's authorship and rights are distinct from the source licences
of the supporting Lean developments.

The project reuses the recovered proof sources from the previous verification
checkpoints and includes the following supporting formal developments:

| Source | Exact revision | Local source prefix |
|---|---|---|
| Dongzhe (Denzel) Zheng, `Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture` | `e457fde9100c9b7226bd4d81af6860f210a531ab` | `Papers/RigidityZheng_` |
| Bryan Gin-ge Chen, `CombinatorialRigidity` | `021c2284bc387efee3c3b20a18eb5f769638b578` | `Papers/RigidityLaman_` |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` | Lake dependency |
| Lean 4 | `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` | `leanprover/lean4:v4.35.0` |

The original copyright and Apache-2.0 notices remain in each adapted file.
Complete supporting licence texts are in `third_party/`. Adaptations include
module visibility, narrower imports, pinned-API proof repairs and the
paper-facing interfaces. A source manifest records exact file hashes.

Original repositories:

- <https://github.com/DongzheZheng/Kiraly-Tanigawa-Body-Pin-Rigidity-Conjecture>
- <https://github.com/bryangingechen/CombinatorialRigidity>
- <https://github.com/leanprover-community/mathlib4>
- <https://github.com/leanprover/lean4>
