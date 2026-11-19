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
def badTest_256 (i : Nat) := badTest (i+256)
cert_badTest_block_5 256 0 0 8 8
cert_badTest_block_5 256 1 8 16 8
cert_badTest_block_5 256 2 16 24 8
cert_badTest_block_5 256 3 24 32 8
cert_badTest_block_5 256 4 32 40 8
cert_badTest_block_5 256 5 40 48 8
cert_badTest_block_5 256 6 48 56 8
cert_badTest_block_5 256 7 56 64 8
cert_badTest_block_5 256 8 64 72 8
cert_badTest_block_5 256 9 72 80 8
cert_badTest_block_5 256 10 80 88 8
cert_badTest_block_5 256 11 88 96 8
cert_badTest_block_5 256 12 96 104 8
cert_badTest_block_5 256 13 104 112 8
cert_badTest_block_5 256 14 112 120 8
cert_badTest_block_5 256 15 120 128 8
cert_badTest_block_5 256 16 128 136 8
cert_badTest_block_5 256 17 136 144 8
cert_badTest_block_5 256 18 144 152 8
cert_badTest_block_5 256 19 152 160 8
cert_badTest_block_5 256 20 160 168 8
cert_badTest_block_5 256 21 168 176 8
cert_badTest_block_5 256 22 176 184 8
cert_badTest_block_5 256 23 184 192 8
cert_badTest_block_5 256 24 192 200 8
cert_badTest_block_5 256 25 200 208 8
cert_badTest_block_5 256 26 208 216 8
cert_badTest_block_5 256 27 216 224 8
cert_badTest_block_5 256 28 224 232 8
cert_badTest_block_5 256 29 232 240 8
cert_badTest_block_5 256 30 240 248 8
cert_badTest_block_5 256 31 248 256 8
theorem badTest_256_complete : Interval badTest_256 0 256 :=
  (interval_append badTest_256 0 128 256
  (interval_append badTest_256 0 64 128
  (interval_append badTest_256 0 32 64
  (interval_append badTest_256 0 16 32
  (interval_append badTest_256 0 8 16
  badTest_256_block_0
  badTest_256_block_1)
  (interval_append badTest_256 16 24 32
  badTest_256_block_2
  badTest_256_block_3))
  (interval_append badTest_256 32 48 64
  (interval_append badTest_256 32 40 48
  badTest_256_block_4
  badTest_256_block_5)
  (interval_append badTest_256 48 56 64
  badTest_256_block_6
  badTest_256_block_7)))
  (interval_append badTest_256 64 96 128
  (interval_append badTest_256 64 80 96
  (interval_append badTest_256 64 72 80
  badTest_256_block_8
  badTest_256_block_9)
  (interval_append badTest_256 80 88 96
  badTest_256_block_10
  badTest_256_block_11))
  (interval_append badTest_256 96 112 128
  (interval_append badTest_256 96 104 112
  badTest_256_block_12
  badTest_256_block_13)
  (interval_append badTest_256 112 120 128
  badTest_256_block_14
  badTest_256_block_15))))
  (interval_append badTest_256 128 192 256
  (interval_append badTest_256 128 160 192
  (interval_append badTest_256 128 144 160
  (interval_append badTest_256 128 136 144
  badTest_256_block_16
  badTest_256_block_17)
  (interval_append badTest_256 144 152 160
  badTest_256_block_18
  badTest_256_block_19))
  (interval_append badTest_256 160 176 192
  (interval_append badTest_256 160 168 176
  badTest_256_block_20
  badTest_256_block_21)
  (interval_append badTest_256 176 184 192
  badTest_256_block_22
  badTest_256_block_23)))
  (interval_append badTest_256 192 224 256
  (interval_append badTest_256 192 208 224
  (interval_append badTest_256 192 200 208
  badTest_256_block_24
  badTest_256_block_25)
  (interval_append badTest_256 208 216 224
  badTest_256_block_26
  badTest_256_block_27))
  (interval_append badTest_256 224 240 256
  (interval_append badTest_256 224 232 240
  badTest_256_block_28
  badTest_256_block_29)
  (interval_append badTest_256 240 248 256
  badTest_256_block_30
  badTest_256_block_31)))))
theorem badTestInterval256 : Interval badTest 256 512 := by
  intro i hlo hhi
  have h := badTest_256_complete (i-256) (Nat.zero_le _) (by omega)
  simpa only [badTest_256, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
