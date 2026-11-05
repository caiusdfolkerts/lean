# Stress–flex orthogonality on spheres and a torus obstruction

This project formalises stress–flex orthogonality for finite cellulations of the two-sphere, the stress–lifting correspondence and analytic continuation behind it, and an explicit embedded nine-vertex torus on which orthogonality fails.

## Verification

With Elan and Git installed, run these commands from this directory. The supplied configuration pins Lean and its dependencies.

```sh
lake exe cache get
lake build
```

The default build checks the proofs and rejects project axioms, proof placeholders, and dependencies beyond `propext`, `Classical.choice`, and `Quot.sound`.

## Main results

| Result | Lean declaration |
| --- | --- |
| Lemma 2, continuous continuation in arbitrary finite dimension | `StressFlex.continuation_orthogonality` |
| Theorem 1, spherical orthogonality | `StressFlex.Spherical.paper_theorem_one_spherical` |
| Theorem 1, embedded torus obstruction | `StressFlex.Torus.stress_flex_counterexample` |
| Proposition 3, quotient correspondence, dimension and analytic continuation | `StressFlex.Spherical.paper_proposition_three` |
| Nonzero torus period and failure of global face potentials | `StressFlex.Torus.lower_cycle_period`, `StressFlex.Torus.no_global_face_potentials` |

The development is in `source/stress_flex.lean`; the period obstruction is in `source/torus_period.lean`.
