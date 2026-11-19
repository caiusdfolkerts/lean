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
def wellFormedTest_512 (i : Nat) := wellFormedTest (i+512)
cert_wellFormedTest_block_5 512 0 0 16 16
cert_wellFormedTest_block_5 512 1 16 32 16
cert_wellFormedTest_block_5 512 2 32 48 16
cert_wellFormedTest_block_5 512 3 48 64 16
cert_wellFormedTest_block_5 512 4 64 80 16
cert_wellFormedTest_block_5 512 5 80 96 16
cert_wellFormedTest_block_5 512 6 96 112 16
cert_wellFormedTest_block_5 512 7 112 128 16
cert_wellFormedTest_block_5 512 8 128 144 16
cert_wellFormedTest_block_5 512 9 144 160 16
cert_wellFormedTest_block_5 512 10 160 176 16
cert_wellFormedTest_block_5 512 11 176 192 16
cert_wellFormedTest_block_5 512 12 192 208 16
cert_wellFormedTest_block_5 512 13 208 224 16
cert_wellFormedTest_block_5 512 14 224 240 16
cert_wellFormedTest_block_5 512 15 240 256 16
theorem wellFormedTest_512_complete : Interval wellFormedTest_512 0 256 :=
  (interval_append wellFormedTest_512 0 128 256
  (interval_append wellFormedTest_512 0 64 128
  (interval_append wellFormedTest_512 0 32 64
  (interval_append wellFormedTest_512 0 16 32
  wellFormedTest_512_block_0
  wellFormedTest_512_block_1)
  (interval_append wellFormedTest_512 32 48 64
  wellFormedTest_512_block_2
  wellFormedTest_512_block_3))
  (interval_append wellFormedTest_512 64 96 128
  (interval_append wellFormedTest_512 64 80 96
  wellFormedTest_512_block_4
  wellFormedTest_512_block_5)
  (interval_append wellFormedTest_512 96 112 128
  wellFormedTest_512_block_6
  wellFormedTest_512_block_7)))
  (interval_append wellFormedTest_512 128 192 256
  (interval_append wellFormedTest_512 128 160 192
  (interval_append wellFormedTest_512 128 144 160
  wellFormedTest_512_block_8
  wellFormedTest_512_block_9)
  (interval_append wellFormedTest_512 160 176 192
  wellFormedTest_512_block_10
  wellFormedTest_512_block_11))
  (interval_append wellFormedTest_512 192 224 256
  (interval_append wellFormedTest_512 192 208 224
  wellFormedTest_512_block_12
  wellFormedTest_512_block_13)
  (interval_append wellFormedTest_512 224 240 256
  wellFormedTest_512_block_14
  wellFormedTest_512_block_15))))
theorem wellFormedTestInterval512 : Interval wellFormedTest 512 768 := by
  intro i hlo hhi
  have h := wellFormedTest_512_complete (i-512) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
