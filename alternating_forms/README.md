# Exterior quotients by two quadrics and their top bidegrees

For a general pair of two-forms, the actual exterior-algebra quotient has the full strip-walk Hilbert series, its binomial-determinant coefficients, and vanishes above ceiling(n/2). For the canonical pencil in odd dimension, the specified exterior monomials form a basis in every degree. Over the complex numbers the top bidegree representation is the actual SL₂ representation Sym^(2p+1)(Sym^q U), with dimension binomial(2p+q+1,q), for all p,q≥0, including zero.

This configuration selects Theorem 1.1, its exact determinant formula, the exterior-basis clause of Theorem 1.3 and full Corollary 5.2, together with the precise support obligations needed to specify those models. Its independent Challenge has 762 lines and 26 compared declarations. The original theorem applications are in `source/PalomarLiteralInterface.lean`; all historical substantive source and licensing are retained.

The companion `alternating_forms_main13` configuration selects the remaining algebraic degeneration/presentation/Koszul clauses of Theorem 1.3. Its verification is a separate exact-commit workflow result. The general geometric Theorem 1.2 and parts of Theorem 4.1 remain explicitly incomplete in the historical README. Other retained multiple-form and positive-characteristic results are not selected here. See `map.json` for exact declaration and paper mappings. The original source README is preserved verbatim in `packaging/README-historical-source.md`.

Preparation record: 2026-11-19T10:01:04.654907+00:00. Exact snapshot `f99b0e657e8e3ca478876ff6a90ea28ef30039be` passed full workflow 44465251883: Comparator, Lean's default kernel, NanoDa and con-ron accepted the selected solution. This metadata successor preserves every Lean source, Comparator configuration and dependency pin byte for byte. Subsequent exact-commit workflow reports determine its own verification outcome. No independent human or editorial approval is claimed.

Build the selected solution with `lake build Solution` using the committed toolchain and dependency manifest.
