module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra06GrowthCacheData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra06
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
def wellFormedTest_1280 (i : Nat) := wellFormedTest (i+1280)
cert_wellFormedTest_block_5 1280 0 0 16 16
cert_wellFormedTest_block_5 1280 1 16 32 16
cert_wellFormedTest_block_5 1280 2 32 48 16
cert_wellFormedTest_block_5 1280 3 48 64 16
cert_wellFormedTest_block_5 1280 4 64 80 16
cert_wellFormedTest_block_5 1280 5 80 96 16
cert_wellFormedTest_block_5 1280 6 96 112 16
cert_wellFormedTest_block_5 1280 7 112 128 16
cert_wellFormedTest_block_5 1280 8 128 144 16
cert_wellFormedTest_block_5 1280 9 144 160 16
cert_wellFormedTest_block_5 1280 10 160 176 16
cert_wellFormedTest_block_5 1280 11 176 192 16
cert_wellFormedTest_block_5 1280 12 192 208 16
cert_wellFormedTest_block_5 1280 13 208 224 16
cert_wellFormedTest_block_5 1280 14 224 240 16
cert_wellFormedTest_block_5 1280 15 240 256 16
theorem wellFormedTest_1280_complete : Interval wellFormedTest_1280 0 256 :=
  (interval_append wellFormedTest_1280 0 128 256
  (interval_append wellFormedTest_1280 0 64 128
  (interval_append wellFormedTest_1280 0 32 64
  (interval_append wellFormedTest_1280 0 16 32
  wellFormedTest_1280_block_0
  wellFormedTest_1280_block_1)
  (interval_append wellFormedTest_1280 32 48 64
  wellFormedTest_1280_block_2
  wellFormedTest_1280_block_3))
  (interval_append wellFormedTest_1280 64 96 128
  (interval_append wellFormedTest_1280 64 80 96
  wellFormedTest_1280_block_4
  wellFormedTest_1280_block_5)
  (interval_append wellFormedTest_1280 96 112 128
  wellFormedTest_1280_block_6
  wellFormedTest_1280_block_7)))
  (interval_append wellFormedTest_1280 128 192 256
  (interval_append wellFormedTest_1280 128 160 192
  (interval_append wellFormedTest_1280 128 144 160
  wellFormedTest_1280_block_8
  wellFormedTest_1280_block_9)
  (interval_append wellFormedTest_1280 160 176 192
  wellFormedTest_1280_block_10
  wellFormedTest_1280_block_11))
  (interval_append wellFormedTest_1280 192 224 256
  (interval_append wellFormedTest_1280 192 208 224
  wellFormedTest_1280_block_12
  wellFormedTest_1280_block_13)
  (interval_append wellFormedTest_1280 224 240 256
  wellFormedTest_1280_block_14
  wellFormedTest_1280_block_15))))
theorem wellFormedTestInterval1280 : Interval wellFormedTest 1280 1536 := by
  intro i hlo hhi
  have h := wellFormedTest_1280_complete (i-1280) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_1280, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
