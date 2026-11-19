module
prelude
public meta import LowerSchemas.FiniteFullSix
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

cert_inverse 000000 0 128 128
cert_inverse 000128 128 256 128
cert_inverse 000256 256 384 128
cert_inverse 000384 384 512 128
cert_inverse 000512 512 640 128
cert_inverse 000640 640 768 128
cert_inverse 000768 768 896 128
cert_inverse 000896 896 1024 128
cert_inverse 001024 1024 1152 128
cert_inverse 001152 1152 1280 128
cert_inverse 001280 1280 1408 128
cert_inverse 001408 1408 1536 128
cert_inverse 001536 1536 1664 128
cert_inverse 001664 1664 1792 128
cert_inverse 001792 1792 1920 128
cert_inverse 001920 1920 2048 128
cert_inverse_join 000000 000256 0 256 128 000128
cert_inverse_join 000256 000512 256 512 384 000384
cert_inverse_join_2 000000 000512 0 512 256 000256
cert_inverse_join 000512 000768 512 768 640 000640
cert_inverse_join 000768 001024 768 1024 896 000896
cert_inverse_join_2 000512 001024 512 1024 768 000768
cert_inverse_join_2 000000 001024 0 1024 512 000512
cert_inverse_join 001024 001280 1024 1280 1152 001152
cert_inverse_join 001280 001536 1280 1536 1408 001408
cert_inverse_join_2 001024 001536 1024 1536 1280 001280
cert_inverse_join 001536 001792 1536 1792 1664 001664
cert_inverse_join 001792 002048 1792 2048 1920 001920
cert_inverse_join_2 001536 002048 1536 2048 1792 001792
cert_inverse_join_2 001024 002048 1024 2048 1536 001536
cert_inverse_join_2 000000 002048 0 2048 1024 001024
cert_inverse_part 000 0 2048 000000 002048
end Papers.RationalityTen.FullSix0FacetEmbedding
