module
prelude
public meta import LowerSchemas.FiniteFullSix
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

cert_inverse 002048 2048 2176 128
cert_inverse 002176 2176 2304 128
cert_inverse 002304 2304 2432 128
cert_inverse 002432 2432 2560 128
cert_inverse 002560 2560 2688 128
cert_inverse 002688 2688 2816 128
cert_inverse 002816 2816 2944 128
cert_inverse 002944 2944 3072 128
cert_inverse 003072 3072 3200 128
cert_inverse 003200 3200 3328 128
cert_inverse 003328 3328 3456 128
cert_inverse 003456 3456 3584 128
cert_inverse 003584 3584 3712 128
cert_inverse 003712 3712 3840 128
cert_inverse 003840 3840 3968 128
cert_inverse 003968 3968 4096 128
cert_inverse_join 002048 002304 2048 2304 2176 002176
cert_inverse_join 002304 002560 2304 2560 2432 002432
cert_inverse_join_2 002048 002560 2048 2560 2304 002304
cert_inverse_join 002560 002816 2560 2816 2688 002688
cert_inverse_join 002816 003072 2816 3072 2944 002944
cert_inverse_join_2 002560 003072 2560 3072 2816 002816
cert_inverse_join_2 002048 003072 2048 3072 2560 002560
cert_inverse_join 003072 003328 3072 3328 3200 003200
cert_inverse_join 003328 003584 3328 3584 3456 003456
cert_inverse_join_2 003072 003584 3072 3584 3328 003328
cert_inverse_join 003584 003840 3584 3840 3712 003712
cert_inverse_join 003840 004096 3840 4096 3968 003968
cert_inverse_join_2 003584 004096 3584 4096 3840 003840
cert_inverse_join_2 003072 004096 3072 4096 3584 003584
cert_inverse_join_2 002048 004096 2048 4096 3072 003072
cert_inverse_part 001 2048 4096 002048 004096
end Papers.RationalityTen.FullSix0FacetEmbedding
