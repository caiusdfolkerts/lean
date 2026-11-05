# The cubical lower bound theorem

This project formalises the principal results of Caius Folkerts’s *The cubical lower bound theorem*. The source includes the supporting mathematics needed for the stated results.

## Verification

With Elan and Git installed, run these commands from this directory. The toolchain and dependency revisions are pinned in the supplied configuration.

```sh
lake exe cache get
lake build
```

The default build includes the mathematical source and checks that the imported project theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`. Downloading the library cache is not itself a proof check.

## Main results

The convex-polytope declarations use `LeanEval.Geometry.PlatonicClassification`. The PL-sphere declarations are in `Cubical.PL.CubeComplex`.

| Paper result | Lean statement |
| --- | --- |
| Theorem 1, `d ≥ 3` | `IsCubical.edge_bound`, `IsCubical.edge_bound_nat` |
| Theorem 1, strengthened, `d ≥ 4` | `IsCubical.strengthened_edge_bound`, `IsCubical.strengthened_edge_bound_nat` |
| Bipartition for convex cubical `d ≥ 3` | `IsCubical.bipartite` |
| Lemma 2 | `IsCubical.generic_local_propagation` |
| Proposition 3 | `IsCubical.generic_facet_determination` |
| Corollary 4, all finite cubical PL spheres in the stated range | `cubical_pl_lower_bound`, `strengthened_edge_bound` |
| Corollary 5, every `1 ≤ i ≤ d−2`, `d ≥ 3` | `IsCubical.face_lower_bound` |
| Corollary 5, facets | `IsCubical.facet_lower_bound` |
| Final strengthened face/facet formulas | `IsCubical.strengthened_face_lower_bound`, `IsCubical.strengthened_facet_lower_bound` |
| Complete cube f-vector and equality cases | `standardCube_faceNumber`, `standardCube_face_equality`, `standardCube_facet_equality` |
| Stacking preserves cubicality | `FacetStacking.isCubical`, `IsStackedCubical.isCubical` |
| Every finite realized stacking sequence attains the bounds | `IsStackedCubical.edge_equality_real`, `IsStackedCubical.face_equality_real`, `IsStackedCubical.facet_equality_real` |
