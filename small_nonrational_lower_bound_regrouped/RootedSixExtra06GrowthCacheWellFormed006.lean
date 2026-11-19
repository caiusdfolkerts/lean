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
def wellFormedTest_1536 (i : Nat) := wellFormedTest (i+1536)
cert_wellFormedTest_block_5 1536 0 0 16 16
cert_wellFormedTest_block_5 1536 1 16 32 16
cert_wellFormedTest_block_5 1536 2 32 48 16
cert_wellFormedTest_block_5 1536 3 48 64 16
cert_wellFormedTest_block_5 1536 4 64 80 16
cert_wellFormedTest_block_5 1536 5 80 96 16
cert_wellFormedTest_block_5 1536 6 96 112 16
cert_wellFormedTest_block_5 1536 7 112 128 16
cert_wellFormedTest_block_5 1536 8 128 144 16
cert_wellFormedTest_block_5 1536 9 144 160 16
cert_wellFormedTest_block_5 1536 10 160 176 16
cert_wellFormedTest_block_5 1536 11 176 192 16
cert_wellFormedTest_block_5 1536 12 192 208 16
cert_wellFormedTest_block_5 1536 13 208 224 16
cert_wellFormedTest_block_5 1536 14 224 240 16
cert_wellFormedTest_block_5 1536 15 240 256 16
theorem wellFormedTest_1536_complete : Interval wellFormedTest_1536 0 256 :=
  (interval_append wellFormedTest_1536 0 128 256
  (interval_append wellFormedTest_1536 0 64 128
  (interval_append wellFormedTest_1536 0 32 64
  (interval_append wellFormedTest_1536 0 16 32
  wellFormedTest_1536_block_0
  wellFormedTest_1536_block_1)
  (interval_append wellFormedTest_1536 32 48 64
  wellFormedTest_1536_block_2
  wellFormedTest_1536_block_3))
  (interval_append wellFormedTest_1536 64 96 128
  (interval_append wellFormedTest_1536 64 80 96
  wellFormedTest_1536_block_4
  wellFormedTest_1536_block_5)
  (interval_append wellFormedTest_1536 96 112 128
  wellFormedTest_1536_block_6
  wellFormedTest_1536_block_7)))
  (interval_append wellFormedTest_1536 128 192 256
  (interval_append wellFormedTest_1536 128 160 192
  (interval_append wellFormedTest_1536 128 144 160
  wellFormedTest_1536_block_8
  wellFormedTest_1536_block_9)
  (interval_append wellFormedTest_1536 160 176 192
  wellFormedTest_1536_block_10
  wellFormedTest_1536_block_11))
  (interval_append wellFormedTest_1536 192 224 256
  (interval_append wellFormedTest_1536 192 208 224
  wellFormedTest_1536_block_12
  wellFormedTest_1536_block_13)
  (interval_append wellFormedTest_1536 224 240 256
  wellFormedTest_1536_block_14
  wellFormedTest_1536_block_15))))
theorem wellFormedTestInterval1536 : Interval wellFormedTest 1536 1792 := by
  intro i hlo hhi
  have h := wellFormedTest_1536_complete (i-1536) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_1536, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
