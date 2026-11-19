module
prelude
public meta import LowerSchemas.FiniteFullSix
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

cert_inverse 006144 6144 6272 128
cert_inverse 006272 6272 6400 128
cert_inverse 006400 6400 6528 128
cert_inverse 006528 6528 6656 128
cert_inverse 006656 6656 6784 128
cert_inverse 006784 6784 6912 128
cert_inverse 006912 6912 7040 128
cert_inverse 007040 7040 7168 128
cert_inverse 007168 7168 7296 128
cert_inverse 007296 7296 7424 128
cert_inverse 007424 7424 7552 128
cert_inverse 007552 7552 7680 128
cert_inverse 007680 7680 7808 128
cert_inverse 007808 7808 7936 128
cert_inverse 007936 7936 8064 128
cert_inverse 008064 8064 8192 128
cert_inverse_join 006144 006400 6144 6400 6272 006272
cert_inverse_join 006400 006656 6400 6656 6528 006528
cert_inverse_join_2 006144 006656 6144 6656 6400 006400
cert_inverse_join 006656 006912 6656 6912 6784 006784
cert_inverse_join 006912 007168 6912 7168 7040 007040
cert_inverse_join_2 006656 007168 6656 7168 6912 006912
cert_inverse_join_2 006144 007168 6144 7168 6656 006656
cert_inverse_join 007168 007424 7168 7424 7296 007296
cert_inverse_join 007424 007680 7424 7680 7552 007552
cert_inverse_join_2 007168 007680 7168 7680 7424 007424
cert_inverse_join 007680 007936 7680 7936 7808 007808
cert_inverse_join 007936 008192 7936 8192 8064 008064
cert_inverse_join_2 007680 008192 7680 8192 7936 007936
cert_inverse_join_2 007168 008192 7168 8192 7680 007680
cert_inverse_join_2 006144 008192 6144 8192 7168 007168
cert_inverse_part 003 6144 8192 006144 008192
end Papers.RationalityTen.FullSix0FacetEmbedding
