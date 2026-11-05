module

public import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Matrix rank and minors

The rank/minor criteria and invariance under field embeddings are imported
from the exact pinned TauCeti source. Previously copied declarations had the
same fully qualified names as that source and collided when the geometric
and algebraic dependencies were imported together. This module re-exports
the actual upstream proofs; it adds no assumptions or replacement axioms.

The source revision and SHA-256 hashes are recorded in
`third_party/TauCeti_provenance.json`.
-/
