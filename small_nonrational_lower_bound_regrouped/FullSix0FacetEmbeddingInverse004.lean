module
prelude
public meta import LowerSchemas.FiniteFullSix
public import FullSix0FacetEmbeddingData

@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.FullSix0FacetEmbedding
open ConcreteGrowth FiniteChecks

cert_inverse 008192 8192 8320 128
cert_inverse 008320 8320 8448 128
cert_inverse 008448 8448 8576 128
cert_inverse 008576 8576 8704 128
cert_inverse 008704 8704 8832 128
cert_inverse 008832 8832 8960 128
cert_inverse 008960 8960 9088 128
cert_inverse 009088 9088 9216 128
cert_inverse 009216 9216 9344 128
cert_inverse 009344 9344 9472 128
cert_inverse 009472 9472 9600 128
cert_inverse 009600 9600 9728 128
cert_inverse 009728 9728 9856 128
cert_inverse 009856 9856 9984 128
cert_inverse 009984 9984 10112 128
cert_inverse 010112 10112 10240 128
cert_inverse_join 008192 008448 8192 8448 8320 008320
cert_inverse_join 008448 008704 8448 8704 8576 008576
cert_inverse_join_2 008192 008704 8192 8704 8448 008448
cert_inverse_join 008704 008960 8704 8960 8832 008832
cert_inverse_join 008960 009216 8960 9216 9088 009088
cert_inverse_join_2 008704 009216 8704 9216 8960 008960
cert_inverse_join_2 008192 009216 8192 9216 8704 008704
cert_inverse_join 009216 009472 9216 9472 9344 009344
cert_inverse_join 009472 009728 9472 9728 9600 009600
cert_inverse_join_2 009216 009728 9216 9728 9472 009472
cert_inverse_join 009728 009984 9728 9984 9856 009856
cert_inverse_join 009984 010240 9984 10240 10112 010112
cert_inverse_join_2 009728 010240 9728 10240 9984 009984
cert_inverse_join_2 009216 010240 9216 10240 9728 009728
cert_inverse_join_2 008192 010240 8192 10240 9216 009216
cert_inverse_part 004 8192 10240 008192 010240
end Papers.RationalityTen.FullSix0FacetEmbedding
