# Characterizations of polymatroidal ideals

This project contains the full Lean4 formalisation for all principal results in my paper *Characterizations of polymatroidal ideals*.

## Verification

If you have Elan and Git installed, run below commands from this directory.

```sh
lake exe cache get
lake build
```

## Main results

Here's a guide to help you navigate this repo! All verified theorems/propositions/corollaries are linked to their corresponding Lean4 declarations in the table below.

| Paper result | Scope retained |
| --- | --- |
| Theorem 1.1; Corollaries 2.7, 2.10, 3.10–3.11 | Both recognition equivalences, literal polynomial ideals and localizations, quotient socles, field independence, and universal pure reverse-lexicographic quotients. |
| Theorem 2.11; Corollary 2.12 | The real generator hull, ordinary integral closure for all polynomial elements, coordinate-prime powers, and the integral-closedness and intersection-type characterizations. |
| Theorems 3.3, 3.6, 3.12 | Genuine linear presentations, prescribed-donor exchange at distance four, sufficient order coverage, and every monomial term order. |
| Proposition 4.1 | The complete nonzero result, the valid closure and finite-length assertions at zero, and the explicit zero-ideal counterexample to the unrestricted regularity equality. |
| Theorems 4.2, 4.5, 4.9 | The exact degree and dimension cutoffs, both localization bands, and the triangular bound for actual graded derived Tor. |
| Propositions 4.3, 4.7, 4.10; Corollary 4.8 | The complete nonlinear deleted-generator strand, single-localization isolators, optimal degrees and first nonlinear positions, and attained minimum numbers of localization tests. |
| Theorems 5.3–5.4; Corollary 5.5 | Exact necessary and sufficient order coverage, all small cases, exact high-degree counts, both lower bounds, the logarithmic upper bound, and literal fixed-degree asymptotics. |
| Theorem 5.6 | The sharp uniform rejection probability, examples attaining it, the small-dimensional cases, and the repeated independent-test bound. |
