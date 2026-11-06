# Barycentric invariance and universal parameters for face rings

This project contains the full Lean4 formalisation for all principal results in my paper *Barycentric invariance and universal parameters for face rings*. 

## Verification

If you have Elan and Git installed, run below commands from this directory.

```sh
lake exe cache get
lake build
```

## Main results

Here's a guide to help you navigate this repo! All verified theorems/propositions/corollaries are linked to their corresponding Lean4 declarations in the table below. Note declaration names use `FourPapers.Universal`.

| Paper result | Formalised content and source |
| --- | --- |
| Theorem 1.1 | The coherent parameter-module comparison for the original quotient rings; `source/theorem11.lean`. |
| Theorem 1.2 | Actual derived Tor, absolute and relative filtrations, both products, equivariance and field representation classes; `source/theorem12.lean`. |
| Theorem 1.3 | Both directions of the factorial-unit criterion, including nonisomorphism without that hypothesis; `source/theorem13.lean`. |
| Theorem 9.4 | The exact factorial scalar ideal, coherent comparison module and first-cohomology obstruction; `source/theorem94.lean`. |
