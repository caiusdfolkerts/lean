module
prelude
public meta import LowerSchemas.BundledChecks
public import RootedSixBase01GrowthCacheData

/- RootedSixBase01GrowthCacheWellFormed056 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest 14336
cert_wellFormedTest_block 14336 0 0 16 16
cert_wellFormedTest_block 14336 1 16 32 16
cert_wellFormedTest_block 14336 2 32 48 16
cert_wellFormedTest_block 14336 3 48 64 16
cert_wellFormedTest_block 14336 4 64 80 16
cert_wellFormedTest_block 14336 5 80 96 16
cert_wellFormedTest_block 14336 6 96 112 16
cert_wellFormedTest_block 14336 7 112 128 16
cert_wellFormedTest_block 14336 8 128 144 16
cert_wellFormedTest_block 14336 9 144 160 16
cert_wellFormedTest_block 14336 10 160 176 16
cert_wellFormedTest_block 14336 11 176 192 16
cert_wellFormedTest_block 14336 12 192 208 16
cert_wellFormedTest_block 14336 13 208 224 16
cert_wellFormedTest_block 14336 14 224 240 16
cert_wellFormedTest_block 14336 15 240 256 16
cert_wellFormedTest_complete 14336 256
cert_wellFormedTestInterval 14336 14592
end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed057 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest 14592
cert_wellFormedTest_block 14592 0 0 16 16
cert_wellFormedTest_block 14592 1 16 32 16
cert_wellFormedTest_block 14592 2 32 48 16
cert_wellFormedTest_block 14592 3 48 64 16
cert_wellFormedTest_block 14592 4 64 80 16
cert_wellFormedTest_block 14592 5 80 96 16
cert_wellFormedTest_block 14592 6 96 112 16
cert_wellFormedTest_block 14592 7 112 128 16
cert_wellFormedTest_block 14592 8 128 144 16
cert_wellFormedTest_block 14592 9 144 160 16
cert_wellFormedTest_block 14592 10 160 176 16
cert_wellFormedTest_block 14592 11 176 192 16
cert_wellFormedTest_block 14592 12 192 208 16
cert_wellFormedTest_block 14592 13 208 224 16
cert_wellFormedTest_block 14592 14 224 240 16
cert_wellFormedTest_block 14592 15 240 256 16
cert_wellFormedTest_complete 14592 256
cert_wellFormedTestInterval 14592 14848
end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed058 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest 14848
cert_wellFormedTest_block 14848 0 0 16 16
cert_wellFormedTest_block 14848 1 16 32 16
cert_wellFormedTest_block 14848 2 32 48 16
cert_wellFormedTest_block 14848 3 48 64 16
cert_wellFormedTest_block 14848 4 64 80 16
cert_wellFormedTest_block 14848 5 80 96 16
cert_wellFormedTest_block 14848 6 96 112 16
cert_wellFormedTest_block 14848 7 112 128 16
cert_wellFormedTest_block 14848 8 128 144 16
cert_wellFormedTest_block 14848 9 144 160 16
cert_wellFormedTest_block 14848 10 160 176 16
cert_wellFormedTest_block 14848 11 176 192 16
cert_wellFormedTest_block 14848 12 192 208 16
cert_wellFormedTest_block 14848 13 208 224 16
cert_wellFormedTest_block 14848 14 224 240 16
cert_wellFormedTest_block 14848 15 240 256 16
cert_wellFormedTest_complete 14848 256
cert_wellFormedTestInterval 14848 15104
end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheWellFormed059 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest 15104
cert_wellFormedTest_block 15104 0 0 16 16
cert_wellFormedTest_block 15104 1 16 32 16
cert_wellFormedTest_block 15104 2 32 48 16
cert_wellFormedTest_block 15104 3 48 64 16
cert_wellFormedTest_block 15104 4 64 80 16
cert_wellFormedTest_block 15104 5 80 96 16
cert_wellFormedTest_block 15104 6 96 112 16
cert_wellFormedTest_block 15104 7 112 128 16
cert_wellFormedTest_block 15104 8 128 142 14
theorem wellFormedTest_15104_complete : Interval wellFormedTest_15104 0 142 :=
  (interval_append wellFormedTest_15104 0 64 142
  (interval_append wellFormedTest_15104 0 32 64
  (interval_append wellFormedTest_15104 0 16 32
  wellFormedTest_15104_block_0
  wellFormedTest_15104_block_1)
  (interval_append wellFormedTest_15104 32 48 64
  wellFormedTest_15104_block_2
  wellFormedTest_15104_block_3))
  (interval_append wellFormedTest_15104 64 96 142
  (interval_append wellFormedTest_15104 64 80 96
  wellFormedTest_15104_block_4
  wellFormedTest_15104_block_5)
  (interval_append wellFormedTest_15104 96 112 142
  wellFormedTest_15104_block_6
  (interval_append wellFormedTest_15104 112 128 142
  wellFormedTest_15104_block_7
  wellFormedTest_15104_block_8))))
cert_wellFormedTestInterval 15104 15246
end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
