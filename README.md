# Frozen volume raw expression diagnostic

Exact immutable source: caiusdfolkerts/research commit 55fdfa7881012bf6d9662704616d90468c2d46f6, project
volume_polynomials, comparator volume_polynomials/comparator.json. Mathematical sources,
selected theorem scope and semantic data remain unchanged.

This deliberately rebuilds that exact source once with the unmodified verifier
CLI pinned14aa8d6b3c2f14a8540605e37144560b9a00e7e7, then examines both retained
exports in the same remote job. It enumerates all reachable raw mismatches and
prints up to six differing raw expression leaves per non-theorem definition,
forty-eight leaves globally. Node text is bounded500characters and recursion
96levels. It uses the same alpha-equivalence equality as ConstantInfo fields,
ignoring binder names/annotations. Paths, differing constants/literals and
bounded fallback nodes are evidence; no source cause is presumed.

This is a diagnostic, not an official reusable preflight, kernel-verification
pass or intake authorization. Only bounded logs/receipts and exact report at
audit are uploaded; no large exports are downloaded. Combined export cap1GiB,
parser2GiB/audit300seconds, unchanged execute budget19800seconds. Historical
Detailed diagnostics and prior receipts remain untouched.

New Expr walker +JSON logging passed a512MiB toolchain-only4.36rc1 fixture;
identical terms, changed numeral/proof constants and irrelevant binder hygiene
were checked. The unchanged export parser/wrapper already ran successfully.
Full integrated helper has not been run locally against either project export.
No local project/Mathlib build was performed. Root owns publication.

Push trigger: palomar-diagnostics/volume-first-diff.
