module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed031GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed031
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest_3 512
cert_cellTest_block_3 512 0 0 8 8
cert_cellTest_block_3 512 1 8 16 8
cert_cellTest_block_3 512 2 16 24 8
cert_cellTest_block_3 512 3 24 32 8
cert_cellTest_block_3 512 4 32 40 8
cert_cellTest_block_3 512 5 40 48 8
cert_cellTest_block_3 512 6 48 56 8
cert_cellTest_block_3 512 7 56 64 8
cert_cellTest_block_3 512 8 64 72 8
cert_cellTest_block_3 512 9 72 80 8
cert_cellTest_block_3 512 10 80 88 8
cert_cellTest_block_3 512 11 88 96 8
cert_cellTest_block_3 512 12 96 104 8
cert_cellTest_block_3 512 13 104 112 8
cert_cellTest_block_3 512 14 112 120 8
cert_cellTest_block_3 512 15 120 128 8
cert_cellTest_block_3 512 16 128 136 8
cert_cellTest_block_3 512 17 136 143 7
theorem cellTest_512_complete : Interval cellTest_512 0 143 :=
  (interval_append cellTest_512 0 72 143
  (interval_append cellTest_512 0 32 72
  (interval_append cellTest_512 0 16 32
  (interval_append cellTest_512 0 8 16
  cellTest_512_block_0
  cellTest_512_block_1)
  (interval_append cellTest_512 16 24 32
  cellTest_512_block_2
  cellTest_512_block_3))
  (interval_append cellTest_512 32 48 72
  (interval_append cellTest_512 32 40 48
  cellTest_512_block_4
  cellTest_512_block_5)
  (interval_append cellTest_512 48 56 72
  cellTest_512_block_6
  (interval_append cellTest_512 56 64 72
  cellTest_512_block_7
  cellTest_512_block_8))))
  (interval_append cellTest_512 72 104 143
  (interval_append cellTest_512 72 88 104
  (interval_append cellTest_512 72 80 88
  cellTest_512_block_9
  cellTest_512_block_10)
  (interval_append cellTest_512 88 96 104
  cellTest_512_block_11
  cellTest_512_block_12))
  (interval_append cellTest_512 104 120 143
  (interval_append cellTest_512 104 112 120
  cellTest_512_block_13
  cellTest_512_block_14)
  (interval_append cellTest_512 120 128 143
  cellTest_512_block_15
  (interval_append cellTest_512 128 136 143
  cellTest_512_block_16
  cellTest_512_block_17)))))
cert_cellTestInterval_2 512 655
end Papers.RationalityTen.RootedCaches.RootedSevenMixed031
