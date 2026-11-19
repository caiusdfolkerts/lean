module
prelude
public meta import LowerSchemas.FiniteRootedSevenPure
public import RootedSevenPure039GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure039
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest_5 512
cert_wellFormedTest_block_3 512 0 0 16 16
cert_wellFormedTest_block_3 512 1 16 32 16
cert_wellFormedTest_block_3 512 2 32 48 16
cert_wellFormedTest_block_3 512 3 48 64 16
cert_wellFormedTest_block_3 512 4 64 80 16
cert_wellFormedTest_block_3 512 5 80 96 16
cert_wellFormedTest_block_3 512 6 96 112 16
cert_wellFormedTest_block_3 512 7 112 128 16
cert_wellFormedTest_block_3 512 8 128 144 16
cert_wellFormedTest_block_3 512 9 144 147 3
theorem wellFormedTest_512_complete : Interval wellFormedTest_512 0 147 :=
  (interval_append wellFormedTest_512 0 80 147
  (interval_append wellFormedTest_512 0 32 80
  (interval_append wellFormedTest_512 0 16 32
  wellFormedTest_512_block_0
  wellFormedTest_512_block_1)
  (interval_append wellFormedTest_512 32 48 80
  wellFormedTest_512_block_2
  (interval_append wellFormedTest_512 48 64 80
  wellFormedTest_512_block_3
  wellFormedTest_512_block_4)))
  (interval_append wellFormedTest_512 80 112 147
  (interval_append wellFormedTest_512 80 96 112
  wellFormedTest_512_block_5
  wellFormedTest_512_block_6)
  (interval_append wellFormedTest_512 112 128 147
  wellFormedTest_512_block_7
  (interval_append wellFormedTest_512 128 144 147
  wellFormedTest_512_block_8
  wellFormedTest_512_block_9))))
cert_wellFormedTestInterval_3 512 659
end Papers.RationalityTen.RootedCaches.RootedSevenPure039
