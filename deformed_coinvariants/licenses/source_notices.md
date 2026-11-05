# Source notices

Original mathematical formalisation and explanatory documentation are by
Caius Folkerts and use the Apache License, Version 2.0, reproduced in
[apache_2_0.txt](apache_2_0.txt).

The `source/TauCeti` directory contains the required dependency subset of
Tau Ceti, recovered with the recorded source revision
`06d5bb4e3ebb737dc6538567f5c53bf8800b9362`. The original authorship and
copyright headers are retained, and its Apache 2.0 license is reproduced in
[tau_ceti_license.txt](tau_ceti_license.txt). Source provenance and any local
repairs are recorded in the recovery inventory.

`PaperVerification/MatrixRank.lean` retains a recovered adaptation of Tau
Ceti's matrix-rank arguments. Its mathematical dependencies are included in
the default audit.

Mathlib and its dependencies are pinned in `lake-manifest.json`; their
individual licenses remain in force. No compiled third-party library binaries
are included in this source package.
