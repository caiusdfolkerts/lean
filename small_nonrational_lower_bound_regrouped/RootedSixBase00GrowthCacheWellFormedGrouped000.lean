module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase00GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest_6 21504
cert_wellFormedTest_block_4 21504 0 0 16 16
cert_wellFormedTest_block_4 21504 1 16 32 16
cert_wellFormedTest_block_4 21504 2 32 48 16
cert_wellFormedTest_block_4 21504 3 48 64 16
cert_wellFormedTest_block_4 21504 4 64 80 16
cert_wellFormedTest_block_4 21504 5 80 96 16
cert_wellFormedTest_block_4 21504 6 96 112 16
cert_wellFormedTest_block_4 21504 7 112 128 16
cert_wellFormedTest_block_4 21504 8 128 144 16
cert_wellFormedTest_block_4 21504 9 144 160 16
cert_wellFormedTest_block_4 21504 10 160 176 16
cert_wellFormedTest_block_4 21504 11 176 192 16
cert_wellFormedTest_block_4 21504 12 192 208 16
cert_wellFormedTest_block_4 21504 13 208 224 16
cert_wellFormedTest_block_4 21504 14 224 240 16
cert_wellFormedTest_block_4 21504 15 240 256 16
cert_wellFormedTest_complete_8 21504
cert_wellFormedTestInterval_4 21504 21760
end Papers.RationalityTen.RootedCaches.RootedSixBase00
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest_6 21760
cert_wellFormedTest_block_4 21760 0 0 16 16
cert_wellFormedTest_block_4 21760 1 16 32 16
cert_wellFormedTest_block_4 21760 2 32 48 16
cert_wellFormedTest_block_4 21760 3 48 64 16
cert_wellFormedTest_block_4 21760 4 64 80 16
cert_wellFormedTest_block_4 21760 5 80 96 16
cert_wellFormedTest_block_4 21760 6 96 112 16
cert_wellFormedTest_block_4 21760 7 112 128 16
cert_wellFormedTest_block_4 21760 8 128 144 16
cert_wellFormedTest_block_4 21760 9 144 160 16
cert_wellFormedTest_block_4 21760 10 160 176 16
cert_wellFormedTest_block_4 21760 11 176 192 16
cert_wellFormedTest_block_4 21760 12 192 208 16
cert_wellFormedTest_block_4 21760 13 208 216 8
theorem wellFormedTest_21760_complete : Interval wellFormedTest_21760 0 216 :=
  (interval_append wellFormedTest_21760 0 112 216
  (interval_append wellFormedTest_21760 0 48 112
  (interval_append wellFormedTest_21760 0 16 48
  wellFormedTest_21760_block_0
  (interval_append wellFormedTest_21760 16 32 48
  wellFormedTest_21760_block_1
  wellFormedTest_21760_block_2))
  (interval_append wellFormedTest_21760 48 80 112
  (interval_append wellFormedTest_21760 48 64 80
  wellFormedTest_21760_block_3
  wellFormedTest_21760_block_4)
  (interval_append wellFormedTest_21760 80 96 112
  wellFormedTest_21760_block_5
  wellFormedTest_21760_block_6)))
  (interval_append wellFormedTest_21760 112 160 216
  (interval_append wellFormedTest_21760 112 128 160
  wellFormedTest_21760_block_7
  (interval_append wellFormedTest_21760 128 144 160
  wellFormedTest_21760_block_8
  wellFormedTest_21760_block_9))
  (interval_append wellFormedTest_21760 160 192 216
  (interval_append wellFormedTest_21760 160 176 192
  wellFormedTest_21760_block_10
  wellFormedTest_21760_block_11)
  (interval_append wellFormedTest_21760 192 208 216
  wellFormedTest_21760_block_12
  wellFormedTest_21760_block_13))))
cert_wellFormedTestInterval_4 21760 21976
end Papers.RationalityTen.RootedCaches.RootedSixBase00
end
end
