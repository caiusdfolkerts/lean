# Ellipsoids are determined by their intrinsic volumes

This project contains the full Lean4 formalisation for all principal results in my paper *Ellipsoids are determined by their intrinsic volumes*.

## Verification

If you have Elan and Git installed, run below commands from this directory.

```sh
lake exe cache get
lake build
```

## Main results

Here's a guide to help you navigate this repo! All verified theorems/propositions/corollaries are linked to their corresponding Lean4 declarations in the table below. Note declaration names use `EllipsoidVerification`.

| Paper result | Lean statement |
| --- | --- |
| Theorem 1.1: reconstruction | `intrinsic_reconstruction` |
| Theorem 1.2: uniform exponent `1/n` | `uniform_holder_recovery` |
| Theorem 1.2: local sharpness at every interior sphere | `sharp_holder_recovery` |
| Equal-volume sharpness for `n ≥ 2` | `sharp_holder_recovery_at_fixed_volume` |
| Theorem 2.1: the full coefficient transform theorem | `coefficient_transform_theorem` |
| Its actual manifold-with-corners embedding | `coefficient_transform_manifold_with_corners` |
| Lemma 3.1: ordered moment kernel | `orderedMomentKernel_posDef` |
| Lemma 4.1: actual coefficient derivative | `fderiv_coefficientTransform_single` |
| Proposition 4.2: rescaled symmetric Jacobian | `symmetricPart_balancedJacobian_posDef` |
| Section 5.1: measured coefficient bounds | `measured_coefficient_box` |
