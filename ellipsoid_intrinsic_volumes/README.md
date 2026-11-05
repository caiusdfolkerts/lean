# Ellipsoids are determined by their intrinsic volumes

This project formalises the principal results of Caius Folkerts’s *Ellipsoids are determined by their intrinsic volumes*. The source includes the supporting mathematics needed for the stated results.

## Verification

With Elan and Git installed, run these commands from this directory. The toolchain and dependency revisions are pinned in the supplied configuration.

```sh
lake exe cache get
lake build
```

The default build includes the mathematical source and checks that the imported project theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. Downloading the library cache is not itself a proof check.

## Main results

Unless otherwise qualified, declaration names use the namespace `EllipsoidVerification`.

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
