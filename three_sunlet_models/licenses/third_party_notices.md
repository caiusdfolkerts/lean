# Third-party notices

## Laurent monomial localization

The proof `Sunlet.LaurentMonomials.additive_monomial_localization`, shipped in
`Sunlet/VerifiedToricGeometry.lean`, adapts
`MonoidAlgebra.isLocalization_away_mapDomainRingHom` from
[Tau Ceti](https://github.com/TauCetiProject/TauCeti/blob/6b896c7c411221eb78639e4be8ead6e479a62893/TauCeti/Algebra/MonoidAlgebra/Localization.lean),
revision `6b896c7c411221eb78639e4be8ead6e479a62893`.

The upstream source carries this notice:

> Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
> Released under Apache 2.0 license as described in the file LICENSE.
> Authors: The Tau Ceti contributors

The adaptation uses additive monoid algebras and additive exponent notation.
Its complete proof is included and rechecked against the pinned Mathlib version.
The [upstream Apache 2.0 license](licenses/TauCeti-Apache-2.0.txt) is included;
the pinned source and license hashes are recorded in
`verification/tauceti_license_source.json`.
