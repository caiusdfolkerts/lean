module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase03GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest_9 5120
cert_cellTest_block_5 5120 0 0 8 8
cert_cellTest_block_5 5120 1 8 16 8
cert_cellTest_block_5 5120 2 16 24 8
cert_cellTest_block_5 5120 3 24 32 8
cert_cellTest_block_5 5120 4 32 40 8
cert_cellTest_block_5 5120 5 40 48 8
cert_cellTest_block_5 5120 6 48 56 8
cert_cellTest_block_5 5120 7 56 64 8
cert_cellTest_block_5 5120 8 64 72 8
cert_cellTest_block_5 5120 9 72 80 8
cert_cellTest_block_5 5120 10 80 88 8
cert_cellTest_block_5 5120 11 88 96 8
cert_cellTest_block_5 5120 12 96 104 8
cert_cellTest_block_5 5120 13 104 112 8
cert_cellTest_block_5 5120 14 112 118 6
theorem cellTest_5120_complete : Interval cellTest_5120 0 118 :=
  (interval_append cellTest_5120 0 56 118
  (interval_append cellTest_5120 0 24 56
  (interval_append cellTest_5120 0 8 24
  cellTest_5120_block_0
  (interval_append cellTest_5120 8 16 24
  cellTest_5120_block_1
  cellTest_5120_block_2))
  (interval_append cellTest_5120 24 40 56
  (interval_append cellTest_5120 24 32 40
  cellTest_5120_block_3
  cellTest_5120_block_4)
  (interval_append cellTest_5120 40 48 56
  cellTest_5120_block_5
  cellTest_5120_block_6)))
  (interval_append cellTest_5120 56 88 118
  (interval_append cellTest_5120 56 72 88
  (interval_append cellTest_5120 56 64 72
  cellTest_5120_block_7
  cellTest_5120_block_8)
  (interval_append cellTest_5120 72 80 88
  cellTest_5120_block_9
  cellTest_5120_block_10))
  (interval_append cellTest_5120 88 104 118
  (interval_append cellTest_5120 88 96 104
  cellTest_5120_block_11
  cellTest_5120_block_12)
  (interval_append cellTest_5120 104 112 118
  cellTest_5120_block_13
  cellTest_5120_block_14))))
cert_cellTestInterval_4 5120 5238
end Papers.RationalityTen.RootedCaches.RootedSixBase03
