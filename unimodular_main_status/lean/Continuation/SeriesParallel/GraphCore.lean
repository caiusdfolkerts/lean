module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Recovery.Unimodular.ProductVectorMatroid
public import Unimodular.SeriesParallelNetworks
public import Unimodular.SeriesParallelK4
public import Unimodular.SeriesParallelGraphMinors

/-!
Compatibility import for the unchanged rooted-network and incidence-graph
definitions. Their original full modules are the sole declaration owners;
this wrapper prevents the transport excerpts from redeclaring them when
all principal results are compiled together.
-/
