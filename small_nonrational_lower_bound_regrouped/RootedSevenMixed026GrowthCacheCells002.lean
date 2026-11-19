module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed026GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed026
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest_3 512
cert_cellTest_block_3 512 0 0 8 8
cert_cellTest_block_3 512 1 8 16 8
cert_cellTest_block_3 512 2 16 24 8
cert_cellTest_block_3 512 3 24 32 8
cert_cellTest_block_3 512 4 32 40 8
cert_cellTest_block_3 512 5 40 44 4
theorem cellTest_512_complete : Interval cellTest_512 0 44 :=
  (interval_append cellTest_512 0 24 44
  (interval_append cellTest_512 0 8 24
  cellTest_512_block_0
  (interval_append cellTest_512 8 16 24
  cellTest_512_block_1
  cellTest_512_block_2))
  (interval_append cellTest_512 24 32 44
  cellTest_512_block_3
  (interval_append cellTest_512 32 40 44
  cellTest_512_block_4
  cellTest_512_block_5)))
cert_cellTestInterval_2 512 556
end Papers.RationalityTen.RootedCaches.RootedSevenMixed026
