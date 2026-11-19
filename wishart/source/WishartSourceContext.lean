module
public import WishartCommonProofWitnesses
/-! Match the exact complex NormedField superclass path measured in the original
source, after the shared proposition witnesses have been elaborated. The whole
record path equality is proved in `WishartSharedProof.complexNormedCommRing_path_eq`.
This changes instance selection syntax, while keeping the actual canonical record. -/
@[expose] public section
attribute [-instance] instCommCStarAlgebraComplex
