module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed025GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed025
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest_3 256
cert_wellFormedTest_block_2 256 0 0 16 16
cert_wellFormedTest_block_2 256 1 16 32 16
cert_wellFormedTest_block_2 256 2 32 48 16
cert_wellFormedTest_block_2 256 3 48 64 16
cert_wellFormedTest_block_2 256 4 64 80 16
cert_wellFormedTest_block_2 256 5 80 96 16
cert_wellFormedTest_block_2 256 6 96 112 16
cert_wellFormedTest_block_2 256 7 112 128 16
cert_wellFormedTest_block_2 256 8 128 144 16
cert_wellFormedTest_block_2 256 9 144 160 16
cert_wellFormedTest_block_2 256 10 160 176 16
cert_wellFormedTest_block_2 256 11 176 192 16
cert_wellFormedTest_block_2 256 12 192 208 16
cert_wellFormedTest_block_2 256 13 208 210 2
theorem wellFormedTest_256_complete : Interval wellFormedTest_256 0 210 :=
  (interval_append wellFormedTest_256 0 112 210
  (interval_append wellFormedTest_256 0 48 112
  (interval_append wellFormedTest_256 0 16 48
  wellFormedTest_256_block_0
  (interval_append wellFormedTest_256 16 32 48
  wellFormedTest_256_block_1
  wellFormedTest_256_block_2))
  (interval_append wellFormedTest_256 48 80 112
  (interval_append wellFormedTest_256 48 64 80
  wellFormedTest_256_block_3
  wellFormedTest_256_block_4)
  (interval_append wellFormedTest_256 80 96 112
  wellFormedTest_256_block_5
  wellFormedTest_256_block_6)))
  (interval_append wellFormedTest_256 112 160 210
  (interval_append wellFormedTest_256 112 128 160
  wellFormedTest_256_block_7
  (interval_append wellFormedTest_256 128 144 160
  wellFormedTest_256_block_8
  wellFormedTest_256_block_9))
  (interval_append wellFormedTest_256 160 192 210
  (interval_append wellFormedTest_256 160 176 192
  wellFormedTest_256_block_10
  wellFormedTest_256_block_11)
  (interval_append wellFormedTest_256 192 208 210
  wellFormedTest_256_block_12
  wellFormedTest_256_block_13))))
cert_wellFormedTestInterval_2 256 466
end Papers.RationalityTen.RootedCaches.RootedSevenMixed025
