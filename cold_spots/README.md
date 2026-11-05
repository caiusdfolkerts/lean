# Universal cold spots of E8 and related lattices

This project formalises the principal results of Caius Folkerts’s *Universal cold spots of E8 and related lattices*. It also proves the affine-isometry orbit claims for $D_n^+$ and $E_7^*$ and the affine Weyl orbit claim for $E_8$.

## Verification

With Elan and Git installed, run these commands from this directory. The toolchain and dependency revisions are pinned in the supplied configuration.

```sh
lake exe cache get
lake build
```

The default build includes the mathematical source and checks all project declarations, including private definitions, for proof placeholders, project axioms and unsafe or partial code. The permitted transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`. Downloading the library cache is not itself a proof check.

## Main results

Unless qualified otherwise, the lattice declarations use `PaperVerification.ColdSpots`; the hyperbolic declarations use `PaperVerification.Hyperbolic`.

| Manuscript result | Lean declarations |
|:---|:---|
| Theorem 1.1 | `lattice_theorem_1_1` |
| Theorem 3.1 | `hyperbolic_geometric_mean_inequality_literal`; `hyperbolic_geometric_mean_equality_literal_iff` |
| Proposition 3.2 | `theta_geometric_mean_inequality_literal`; `theta_geometric_mean_equality_literal_iff` |
| Theorem 3.3 | `dPlusGaussian_minimum`; `dPlusGaussian_eq_min_iff_paperHalfGrid`; `gaussian_E8_minimum_iff_paper_families` |
| Proposition 3.4 | `dPlus_squared_covering_radius`; `isDeepHole_dPlus_iff_paperHalfGrid`; `isDeepHole_E8_iff_paper` |
| Proposition 6.1 | `rational_orthogonal_lattice_projection_transfer` |
| Proposition 7.1 | `lattice_diagonal_gluing` |
| Theorem 6.2 and (26) | `e7Dual_gaussian_minimum`; `e7_covering_radius`; `isE7DeepHole_iff_paper` |
| Section 7, (28) and full root union | `bw16_gaussian_minimum_literal`; `bw16_deepHole_iff_root_union`; `bw16_gaussian_equality_iff_root_union` |
| Proposition 8.1 | `eisenstein_cubic_identity`; `eisenstein_product_minimum`; `eisenstein_product_equality_iff` |
| Section 8.3 and (32) | `e6_gaussian_minimum`; `e6_cold_spot_description`; `e6_deep_hole_description` |
| Introduction tables | `lattice_covering_radius_table`; `lattice_translation_class_table` |
| Corollary 1.2 | `lattice_corollary_1_2`; `lattice_corollary_1_2_extended` |
| Affine-isometry orbits | `dn_deep_holes_single_affine_orbit`; `e7_deep_holes_single_affine_orbit` |
| Affine Weyl orbit of E8 holes | `e8_deep_holes_single_affine_weyl_orbit` |
