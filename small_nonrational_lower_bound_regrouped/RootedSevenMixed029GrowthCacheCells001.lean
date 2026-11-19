module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed029GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed029
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest_3 256
cert_cellTest_block_3 256 0 0 8 8
cert_cellTest_block_3 256 1 8 16 8
cert_cellTest_block_3 256 2 16 24 8
cert_cellTest_block_3 256 3 24 32 8
cert_cellTest_block_3 256 4 32 40 8
cert_cellTest_block_3 256 5 40 48 8
cert_cellTest_block_3 256 6 48 56 8
cert_cellTest_block_3 256 7 56 64 8
cert_cellTest_block_3 256 8 64 72 8
cert_cellTest_block_3 256 9 72 80 8
cert_cellTest_block_3 256 10 80 88 8
cert_cellTest_block_3 256 11 88 96 8
cert_cellTest_block_3 256 12 96 104 8
cert_cellTest_block_3 256 13 104 112 8
cert_cellTest_block_3 256 14 112 120 8
theorem cellTest_256_complete : Interval cellTest_256 0 120 :=
  (interval_append cellTest_256 0 56 120
  (interval_append cellTest_256 0 24 56
  (interval_append cellTest_256 0 8 24
  cellTest_256_block_0
  (interval_append cellTest_256 8 16 24
  cellTest_256_block_1
  cellTest_256_block_2))
  (interval_append cellTest_256 24 40 56
  (interval_append cellTest_256 24 32 40
  cellTest_256_block_3
  cellTest_256_block_4)
  (interval_append cellTest_256 40 48 56
  cellTest_256_block_5
  cellTest_256_block_6)))
  (interval_append cellTest_256 56 88 120
  (interval_append cellTest_256 56 72 88
  (interval_append cellTest_256 56 64 72
  cellTest_256_block_7
  cellTest_256_block_8)
  (interval_append cellTest_256 72 80 88
  cellTest_256_block_9
  cellTest_256_block_10))
  (interval_append cellTest_256 88 104 120
  (interval_append cellTest_256 88 96 104
  cellTest_256_block_11
  cellTest_256_block_12)
  (interval_append cellTest_256 104 112 120
  cellTest_256_block_13
  cellTest_256_block_14))))
cert_cellTestInterval_2 256 376
end Papers.RationalityTen.RootedCaches.RootedSevenMixed029
