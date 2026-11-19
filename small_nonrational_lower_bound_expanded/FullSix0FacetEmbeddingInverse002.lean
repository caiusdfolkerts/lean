module
prelude
public meta import LowerSchemas.FiniteFullSix
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

cert_inverse 004096 4096 4224 128
cert_inverse 004224 4224 4352 128
cert_inverse 004352 4352 4480 128
cert_inverse 004480 4480 4608 128
cert_inverse 004608 4608 4736 128
cert_inverse 004736 4736 4864 128
cert_inverse 004864 4864 4992 128
cert_inverse 004992 4992 5120 128
cert_inverse 005120 5120 5248 128
cert_inverse 005248 5248 5376 128
cert_inverse 005376 5376 5504 128
cert_inverse 005504 5504 5632 128
cert_inverse 005632 5632 5760 128
cert_inverse 005760 5760 5888 128
cert_inverse 005888 5888 6016 128
cert_inverse 006016 6016 6144 128
cert_inverse_join 004096 004352 4096 4352 4224 004224
cert_inverse_join 004352 004608 4352 4608 4480 004480
cert_inverse_join_2 004096 004608 4096 4608 4352 004352
cert_inverse_join 004608 004864 4608 4864 4736 004736
cert_inverse_join 004864 005120 4864 5120 4992 004992
cert_inverse_join_2 004608 005120 4608 5120 4864 004864
cert_inverse_join_2 004096 005120 4096 5120 4608 004608
cert_inverse_join 005120 005376 5120 5376 5248 005248
cert_inverse_join 005376 005632 5376 5632 5504 005504
cert_inverse_join_2 005120 005632 5120 5632 5376 005376
cert_inverse_join 005632 005888 5632 5888 5760 005760
cert_inverse_join 005888 006144 5888 6144 6016 006016
cert_inverse_join_2 005632 006144 5632 6144 5888 005888
cert_inverse_join_2 005120 006144 5120 6144 5632 005632
cert_inverse_join_2 004096 006144 4096 6144 5120 005120
cert_inverse_part 002 4096 6144 004096 006144
end Papers.RationalityTen.FullSix0FacetEmbedding
