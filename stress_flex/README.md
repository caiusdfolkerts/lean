# Stress–flex orthogonality on spheres and a torus obstruction

This project contains the full Lean4 formalisation for all principal results in my paper *Stress–flex orthogonality on spheres and a torus obstruction*.

## Verification

If you have Elan and Git installed, run below commands from this directory.

```sh
lake exe cache get
lake build
```

## Main results

Here's a guide to help you navigate this repo! All verified theorems/propositions/corollaries are linked to their corresponding Lean4 declarations in the table below.

| Result | Lean declaration |
| --- | --- |
| Lemma 2, continuous continuation in arbitrary finite dimension | `StressFlex.continuation_orthogonality` |
| Theorem 1, spherical orthogonality | `StressFlex.Spherical.paper_theorem_one_spherical` |
| Theorem 1, embedded torus obstruction | `StressFlex.Torus.stress_flex_counterexample` |
| Proposition 3, quotient correspondence, dimension and analytic continuation | `StressFlex.Spherical.paper_proposition_three` |
| Nonzero torus period and failure of global face potentials | `StressFlex.Torus.lower_cycle_period`, `StressFlex.Torus.no_global_face_potentials` |
