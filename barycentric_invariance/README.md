# Barycentric invariance and universal parameters for face rings

This project formalises the principal results of Caius Folkerts’s *Barycentric invariance and universal parameters for face rings*. It covers Theorems 1.1–1.3 and 9.4. The stronger naturality assertion in Theorem 9.1 is outside this formalisation.

## Verification

With Elan and Git installed, run these commands from this directory. The toolchain and dependency revisions are pinned in the supplied configuration.

```sh
lake exe cache get
lake build
```

The default build includes the mathematical source and checks that the imported project theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. Downloading the library cache is not itself a proof check.

## Main results

Unless otherwise qualified, declaration names use the namespace `FourPapers.Universal`.

| Paper result | Formalised content and source |
| --- | --- |
| Theorem 1.1 | The coherent parameter-module comparison for the original quotient rings; `source/theorem11.lean`. |
| Theorem 1.2 | Actual derived Tor, absolute and relative filtrations, both products, equivariance and field representation classes; `source/theorem12.lean`. |
| Theorem 1.3 | Both directions of the factorial-unit criterion, including nonisomorphism without that hypothesis; `source/theorem13.lean`. |
| Theorem 9.4 | The exact factorial scalar ideal, coherent comparison module and first-cohomology obstruction; `source/theorem94.lean`. |
