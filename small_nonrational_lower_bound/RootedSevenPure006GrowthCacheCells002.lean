module
prelude
public meta import LowerSchemas.FiniteRootedSevenPure
public import RootedSevenPure006GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure006
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest_6 512
cert_cellTest_block_4 512 0 0 8 8
cert_cellTest_block_4 512 1 8 16 8
cert_cellTest_block_4 512 2 16 24 8
cert_cellTest_block_4 512 3 24 32 8
cert_cellTest_block_4 512 4 32 40 8
cert_cellTest_block_4 512 5 40 48 8
cert_cellTest_block_4 512 6 48 56 8
cert_cellTest_block_4 512 7 56 64 8
cert_cellTest_block_4 512 8 64 72 8
cert_cellTest_block_4 512 9 72 74 2
theorem cellTest_512_complete : Interval cellTest_512 0 74 :=
  (interval_append cellTest_512 0 40 74
  (interval_append cellTest_512 0 16 40
  (interval_append cellTest_512 0 8 16
  cellTest_512_block_0
  cellTest_512_block_1)
  (interval_append cellTest_512 16 24 40
  cellTest_512_block_2
  (interval_append cellTest_512 24 32 40
  cellTest_512_block_3
  cellTest_512_block_4)))
  (interval_append cellTest_512 40 56 74
  (interval_append cellTest_512 40 48 56
  cellTest_512_block_5
  cellTest_512_block_6)
  (interval_append cellTest_512 56 64 74
  cellTest_512_block_7
  (interval_append cellTest_512 64 72 74
  cellTest_512_block_8
  cellTest_512_block_9))))
cert_cellTestInterval_3 512 586
end Papers.RationalityTen.RootedCaches.RootedSevenPure006
