module
prelude
public meta import LowerSchemas.FiniteFullSix
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

cert_inverse 036864 36864 36992 128
cert_inverse 036992 36992 37120 128
cert_inverse 037120 37120 37248 128
cert_inverse 037248 37248 37376 128
cert_inverse 037376 37376 37504 128
cert_inverse 037504 37504 37632 128
cert_inverse 037632 37632 37760 128
cert_inverse 037760 37760 37800 40
cert_inverse_join 036864 037120 36864 37120 36992 036992
cert_inverse_join 037120 037376 37120 37376 37248 037248
cert_inverse_join_2 036864 037376 36864 37376 37120 037120
cert_inverse_join 037376 037632 37376 37632 37504 037504
cert_inverse_join 037632 037800 37632 37800 37760 037760
cert_inverse_join_2 037376 037800 37376 37800 37632 037632
cert_inverse_join_2 036864 037800 36864 37800 37376 037376
cert_inverse_part 018 36864 37800 036864 037800
end Papers.RationalityTen.FullSix0FacetEmbedding
