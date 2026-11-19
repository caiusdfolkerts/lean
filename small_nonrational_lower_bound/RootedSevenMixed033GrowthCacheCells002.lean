module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed033GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed033
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest_3 512
cert_cellTest_block_3 512 0 0 8 8
cert_cellTest_block_3 512 1 8 16 8
cert_cellTest_block_3 512 2 16 17 1
theorem cellTest_512_complete : Interval cellTest_512 0 17 :=
  (interval_append cellTest_512 0 8 17
  cellTest_512_block_0
  (interval_append cellTest_512 8 16 17
  cellTest_512_block_1
  cellTest_512_block_2))
cert_cellTestInterval_2 512 529
end Papers.RationalityTen.RootedCaches.RootedSevenMixed033
