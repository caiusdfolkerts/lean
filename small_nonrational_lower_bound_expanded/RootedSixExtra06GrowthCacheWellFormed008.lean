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
def wellFormedTest_2048 (i : Nat) := wellFormedTest (i+2048)
cert_wellFormedTest_block_5 2048 0 0 16 16
cert_wellFormedTest_block_5 2048 1 16 32 16
cert_wellFormedTest_block_5 2048 2 32 48 16
cert_wellFormedTest_block_5 2048 3 48 64 16
cert_wellFormedTest_block_5 2048 4 64 80 16
cert_wellFormedTest_block_5 2048 5 80 96 16
cert_wellFormedTest_block_5 2048 6 96 112 16
cert_wellFormedTest_block_5 2048 7 112 128 16
cert_wellFormedTest_block_5 2048 8 128 144 16
cert_wellFormedTest_block_5 2048 9 144 160 16
cert_wellFormedTest_block_5 2048 10 160 176 16
cert_wellFormedTest_block_5 2048 11 176 192 16
cert_wellFormedTest_block_5 2048 12 192 208 16
cert_wellFormedTest_block_5 2048 13 208 224 16
cert_wellFormedTest_block_5 2048 14 224 240 16
cert_wellFormedTest_block_5 2048 15 240 252 12
theorem wellFormedTest_2048_complete : Interval wellFormedTest_2048 0 252 :=
  (interval_append wellFormedTest_2048 0 128 252
  (interval_append wellFormedTest_2048 0 64 128
  (interval_append wellFormedTest_2048 0 32 64
  (interval_append wellFormedTest_2048 0 16 32
  wellFormedTest_2048_block_0
  wellFormedTest_2048_block_1)
  (interval_append wellFormedTest_2048 32 48 64
  wellFormedTest_2048_block_2
  wellFormedTest_2048_block_3))
  (interval_append wellFormedTest_2048 64 96 128
  (interval_append wellFormedTest_2048 64 80 96
  wellFormedTest_2048_block_4
  wellFormedTest_2048_block_5)
  (interval_append wellFormedTest_2048 96 112 128
  wellFormedTest_2048_block_6
  wellFormedTest_2048_block_7)))
  (interval_append wellFormedTest_2048 128 192 252
  (interval_append wellFormedTest_2048 128 160 192
  (interval_append wellFormedTest_2048 128 144 160
  wellFormedTest_2048_block_8
  wellFormedTest_2048_block_9)
  (interval_append wellFormedTest_2048 160 176 192
  wellFormedTest_2048_block_10
  wellFormedTest_2048_block_11))
  (interval_append wellFormedTest_2048 192 224 252
  (interval_append wellFormedTest_2048 192 208 224
  wellFormedTest_2048_block_12
  wellFormedTest_2048_block_13)
  (interval_append wellFormedTest_2048 224 240 252
  wellFormedTest_2048_block_14
  wellFormedTest_2048_block_15))))
theorem wellFormedTestInterval2048 : Interval wellFormedTest 2048 2300 := by
  intro i hlo hhi
  have h := wellFormedTest_2048_complete (i-2048) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_2048, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
