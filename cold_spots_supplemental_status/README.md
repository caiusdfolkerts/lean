# Exact cold-spot minima and translation classes

This supplement states the exact Gaussian minimum values, printed equality loci, and deep-hole translation-class counts for E6, E8, E7 dual, BW16, and every even D_n plus in the paper's range.

The separate `cold_spots` entry covers Theorem1.1, Corollary1.2, and the squared covering radii. Its verified, submitted snapshot is unchanged. This entry supplies the quantitative conclusions omitted from that entry's comparison scope.

`Challenge.lean` imports only pinned canonical Mathlib and defines all lattice sets, squared Euclidean distances, Gaussian series, coordinate families and translation quotients literally. `Solution.lean` repeats those definitions and applies the substantive proofs imported through `release_all`. The complete original proof source and paper are included. The exact independent Challenge passed pinned canonical remote elaboration in run44360360113. Its18 intentional theorem placeholders only check statement interfaces; the new Solution wrappers, Comparator and independent kernel checks remain pending.

| Paper result | Compared conclusions |
|---|---|
| Introduction table | E6:2, E8:135, E7 dual:36, BW16:120, D_n plus:choose(n,n/2) for every even n>8 |
| Theorem3.3 and Equation10 | Attained minimum in every even n>=8; exact half-grid equality set for n>8; all three dimension-eight coordinate families |
| Theorem6.2 and Equation26 | E7 dual minimum formula and complete equality/deep-hole descriptions in the actual zero-sum hyperplane |
| Equation28 and Section7.5 | BW16 attained minimum and full equality/deep-hole union over every actual E8 root |
| Equation32 and Section8.3 | E6 attained minimum and complete equality/deep-hole loci from permutations and lattice translations of the Eisenstein witness |

Every Gaussian parameter is positive. No bounded coordinate enumeration or selected finite set replaces an ambient equality locus. The dimension conditions of each result are retained.

The class counts use the ambient additive quotient by the closure of the explicit lattice set, restricted to classes containing an actual real deep hole. The Solution proves that each closure equals the source's actual lattice subgroup. Thus these are counts of full translation classes, rather than counts of an asserted list of representatives.

All semantic definitions have their displayed mathematical values. Six additional compared theorems supply the proof fields for the integer embedding, zero-sum subspace and orthogonal projection. There are no definition holes.

The proof source comes from `caiusdfolkerts/research` baseline `e0696fddcd3d10b5d6461e62e9b2f02c4195be37`, through the already verified Cold Spots snapshot `9fcbca1143471e6e25c337def9897b58377e0b4c`. That source snapshot's supporting proof-field normalization and optional audit-report persistence repairs are retained. These do not imply verification of the new independent Challenge or its wrappers. The paper retains its original copyright; code is Apache-2.0, with original notices preserved.

The paper discloses GPT-6 Astra, GPT-5.6 Sol and Kimi K3 assistance in developing its proofs. OpenAI Codex assisted this packaging and scope audit. Full earlier prompt history was not reconstructed.

With the pinned Lean/Mathlib toolchain installed, the ordinary targets are `lake build Challenge Solution`. Palomar's exact-commit full workflow, Comparator and independent kernel checks remain required before intake.

The first full supplemental build compiled the substantive source, then rejected
two new closure-transport wrappers: an expensive definitional `change` and an
unexposed canonical Real instance in the E7 type transport. The revision uses
explicit carrier equalities and canonical closure congruence, with Mathlib
import-all in the Solution. The Challenge and mathematical statements are
unchanged; the repaired wrappers still require full preflight.
