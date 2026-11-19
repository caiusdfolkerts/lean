module
prelude
public meta import LowerSchemas.BundledChecks
public import RootedSixExtra02GrowthCacheData

/- RootedSixExtra02GrowthCacheBad006 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 1536
cert_badTest_block 1536 0 0 8 8
cert_badTest_block 1536 1 8 16 8
cert_badTest_block 1536 2 16 24 8
cert_badTest_block 1536 3 24 32 8
cert_badTest_block 1536 4 32 40 8
cert_badTest_block 1536 5 40 48 8
cert_badTest_block 1536 6 48 56 8
cert_badTest_block 1536 7 56 64 8
cert_badTest_block 1536 8 64 72 8
cert_badTest_block 1536 9 72 80 8
cert_badTest_block 1536 10 80 88 8
cert_badTest_block 1536 11 88 96 8
cert_badTest_block 1536 12 96 104 8
cert_badTest_block 1536 13 104 112 8
cert_badTest_block 1536 14 112 120 8
cert_badTest_block 1536 15 120 128 8
cert_badTest_block 1536 16 128 136 8
cert_badTest_block 1536 17 136 144 8
cert_badTest_block 1536 18 144 152 8
cert_badTest_block 1536 19 152 160 8
cert_badTest_block 1536 20 160 168 8
cert_badTest_block 1536 21 168 176 8
cert_badTest_block 1536 22 176 184 8
cert_badTest_block 1536 23 184 192 8
cert_badTest_block 1536 24 192 200 8
cert_badTest_block 1536 25 200 208 8
cert_badTest_block 1536 26 208 216 8
cert_badTest_block 1536 27 216 224 8
cert_badTest_block 1536 28 224 232 8
cert_badTest_block 1536 29 232 240 8
cert_badTest_block 1536 30 240 248 8
cert_badTest_block 1536 31 248 256 8
theorem badTest_1536_complete : Interval badTest_1536 0 256 :=
  (interval_append badTest_1536 0 128 256
  (interval_append badTest_1536 0 64 128
  (interval_append badTest_1536 0 32 64
  (interval_append badTest_1536 0 16 32
  (interval_append badTest_1536 0 8 16
  badTest_1536_block_0
  badTest_1536_block_1)
  (interval_append badTest_1536 16 24 32
  badTest_1536_block_2
  badTest_1536_block_3))
  (interval_append badTest_1536 32 48 64
  (interval_append badTest_1536 32 40 48
  badTest_1536_block_4
  badTest_1536_block_5)
  (interval_append badTest_1536 48 56 64
  badTest_1536_block_6
  badTest_1536_block_7)))
  (interval_append badTest_1536 64 96 128
  (interval_append badTest_1536 64 80 96
  (interval_append badTest_1536 64 72 80
  badTest_1536_block_8
  badTest_1536_block_9)
  (interval_append badTest_1536 80 88 96
  badTest_1536_block_10
  badTest_1536_block_11))
  (interval_append badTest_1536 96 112 128
  (interval_append badTest_1536 96 104 112
  badTest_1536_block_12
  badTest_1536_block_13)
  (interval_append badTest_1536 112 120 128
  badTest_1536_block_14
  badTest_1536_block_15))))
  (interval_append badTest_1536 128 192 256
  (interval_append badTest_1536 128 160 192
  (interval_append badTest_1536 128 144 160
  (interval_append badTest_1536 128 136 144
  badTest_1536_block_16
  badTest_1536_block_17)
  (interval_append badTest_1536 144 152 160
  badTest_1536_block_18
  badTest_1536_block_19))
  (interval_append badTest_1536 160 176 192
  (interval_append badTest_1536 160 168 176
  badTest_1536_block_20
  badTest_1536_block_21)
  (interval_append badTest_1536 176 184 192
  badTest_1536_block_22
  badTest_1536_block_23)))
  (interval_append badTest_1536 192 224 256
  (interval_append badTest_1536 192 208 224
  (interval_append badTest_1536 192 200 208
  badTest_1536_block_24
  badTest_1536_block_25)
  (interval_append badTest_1536 208 216 224
  badTest_1536_block_26
  badTest_1536_block_27))
  (interval_append badTest_1536 224 240 256
  (interval_append badTest_1536 224 232 240
  badTest_1536_block_28
  badTest_1536_block_29)
  (interval_append badTest_1536 240 248 256
  badTest_1536_block_30
  badTest_1536_block_31)))))
cert_badTestInterval 1536 1792
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad007 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 1792
cert_badTest_block 1792 0 0 8 8
cert_badTest_block 1792 1 8 16 8
cert_badTest_block 1792 2 16 24 8
cert_badTest_block 1792 3 24 32 8
cert_badTest_block 1792 4 32 40 8
cert_badTest_block 1792 5 40 48 8
cert_badTest_block 1792 6 48 56 8
cert_badTest_block 1792 7 56 64 8
cert_badTest_block 1792 8 64 72 8
cert_badTest_block 1792 9 72 80 8
cert_badTest_block 1792 10 80 88 8
cert_badTest_block 1792 11 88 96 8
cert_badTest_block 1792 12 96 104 8
cert_badTest_block 1792 13 104 112 8
cert_badTest_block 1792 14 112 120 8
cert_badTest_block 1792 15 120 128 8
cert_badTest_block 1792 16 128 136 8
cert_badTest_block 1792 17 136 144 8
cert_badTest_block 1792 18 144 152 8
cert_badTest_block 1792 19 152 160 8
cert_badTest_block 1792 20 160 168 8
cert_badTest_block 1792 21 168 176 8
cert_badTest_block 1792 22 176 184 8
cert_badTest_block 1792 23 184 192 8
cert_badTest_block 1792 24 192 200 8
cert_badTest_block 1792 25 200 208 8
cert_badTest_block 1792 26 208 216 8
cert_badTest_block 1792 27 216 224 8
cert_badTest_block 1792 28 224 232 8
cert_badTest_block 1792 29 232 240 8
cert_badTest_block 1792 30 240 248 8
cert_badTest_block 1792 31 248 256 8
theorem badTest_1792_complete : Interval badTest_1792 0 256 :=
  (interval_append badTest_1792 0 128 256
  (interval_append badTest_1792 0 64 128
  (interval_append badTest_1792 0 32 64
  (interval_append badTest_1792 0 16 32
  (interval_append badTest_1792 0 8 16
  badTest_1792_block_0
  badTest_1792_block_1)
  (interval_append badTest_1792 16 24 32
  badTest_1792_block_2
  badTest_1792_block_3))
  (interval_append badTest_1792 32 48 64
  (interval_append badTest_1792 32 40 48
  badTest_1792_block_4
  badTest_1792_block_5)
  (interval_append badTest_1792 48 56 64
  badTest_1792_block_6
  badTest_1792_block_7)))
  (interval_append badTest_1792 64 96 128
  (interval_append badTest_1792 64 80 96
  (interval_append badTest_1792 64 72 80
  badTest_1792_block_8
  badTest_1792_block_9)
  (interval_append badTest_1792 80 88 96
  badTest_1792_block_10
  badTest_1792_block_11))
  (interval_append badTest_1792 96 112 128
  (interval_append badTest_1792 96 104 112
  badTest_1792_block_12
  badTest_1792_block_13)
  (interval_append badTest_1792 112 120 128
  badTest_1792_block_14
  badTest_1792_block_15))))
  (interval_append badTest_1792 128 192 256
  (interval_append badTest_1792 128 160 192
  (interval_append badTest_1792 128 144 160
  (interval_append badTest_1792 128 136 144
  badTest_1792_block_16
  badTest_1792_block_17)
  (interval_append badTest_1792 144 152 160
  badTest_1792_block_18
  badTest_1792_block_19))
  (interval_append badTest_1792 160 176 192
  (interval_append badTest_1792 160 168 176
  badTest_1792_block_20
  badTest_1792_block_21)
  (interval_append badTest_1792 176 184 192
  badTest_1792_block_22
  badTest_1792_block_23)))
  (interval_append badTest_1792 192 224 256
  (interval_append badTest_1792 192 208 224
  (interval_append badTest_1792 192 200 208
  badTest_1792_block_24
  badTest_1792_block_25)
  (interval_append badTest_1792 208 216 224
  badTest_1792_block_26
  badTest_1792_block_27))
  (interval_append badTest_1792 224 240 256
  (interval_append badTest_1792 224 232 240
  badTest_1792_block_28
  badTest_1792_block_29)
  (interval_append badTest_1792 240 248 256
  badTest_1792_block_30
  badTest_1792_block_31)))))
cert_badTestInterval 1792 2048
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad008 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 2048
cert_badTest_block 2048 0 0 8 8
cert_badTest_block 2048 1 8 16 8
cert_badTest_block 2048 2 16 24 8
cert_badTest_block 2048 3 24 32 8
cert_badTest_block 2048 4 32 40 8
cert_badTest_block 2048 5 40 48 8
cert_badTest_block 2048 6 48 56 8
cert_badTest_block 2048 7 56 64 8
cert_badTest_block 2048 8 64 72 8
cert_badTest_block 2048 9 72 80 8
cert_badTest_block 2048 10 80 88 8
cert_badTest_block 2048 11 88 96 8
cert_badTest_block 2048 12 96 104 8
cert_badTest_block 2048 13 104 112 8
cert_badTest_block 2048 14 112 120 8
cert_badTest_block 2048 15 120 128 8
cert_badTest_block 2048 16 128 136 8
cert_badTest_block 2048 17 136 144 8
cert_badTest_block 2048 18 144 152 8
cert_badTest_block 2048 19 152 160 8
cert_badTest_block 2048 20 160 168 8
cert_badTest_block 2048 21 168 176 8
cert_badTest_block 2048 22 176 184 8
cert_badTest_block 2048 23 184 192 8
cert_badTest_block 2048 24 192 200 8
cert_badTest_block 2048 25 200 208 8
cert_badTest_block 2048 26 208 216 8
cert_badTest_block 2048 27 216 224 8
cert_badTest_block 2048 28 224 232 8
cert_badTest_block 2048 29 232 240 8
cert_badTest_block 2048 30 240 248 8
cert_badTest_block 2048 31 248 256 8
theorem badTest_2048_complete : Interval badTest_2048 0 256 :=
  (interval_append badTest_2048 0 128 256
  (interval_append badTest_2048 0 64 128
  (interval_append badTest_2048 0 32 64
  (interval_append badTest_2048 0 16 32
  (interval_append badTest_2048 0 8 16
  badTest_2048_block_0
  badTest_2048_block_1)
  (interval_append badTest_2048 16 24 32
  badTest_2048_block_2
  badTest_2048_block_3))
  (interval_append badTest_2048 32 48 64
  (interval_append badTest_2048 32 40 48
  badTest_2048_block_4
  badTest_2048_block_5)
  (interval_append badTest_2048 48 56 64
  badTest_2048_block_6
  badTest_2048_block_7)))
  (interval_append badTest_2048 64 96 128
  (interval_append badTest_2048 64 80 96
  (interval_append badTest_2048 64 72 80
  badTest_2048_block_8
  badTest_2048_block_9)
  (interval_append badTest_2048 80 88 96
  badTest_2048_block_10
  badTest_2048_block_11))
  (interval_append badTest_2048 96 112 128
  (interval_append badTest_2048 96 104 112
  badTest_2048_block_12
  badTest_2048_block_13)
  (interval_append badTest_2048 112 120 128
  badTest_2048_block_14
  badTest_2048_block_15))))
  (interval_append badTest_2048 128 192 256
  (interval_append badTest_2048 128 160 192
  (interval_append badTest_2048 128 144 160
  (interval_append badTest_2048 128 136 144
  badTest_2048_block_16
  badTest_2048_block_17)
  (interval_append badTest_2048 144 152 160
  badTest_2048_block_18
  badTest_2048_block_19))
  (interval_append badTest_2048 160 176 192
  (interval_append badTest_2048 160 168 176
  badTest_2048_block_20
  badTest_2048_block_21)
  (interval_append badTest_2048 176 184 192
  badTest_2048_block_22
  badTest_2048_block_23)))
  (interval_append badTest_2048 192 224 256
  (interval_append badTest_2048 192 208 224
  (interval_append badTest_2048 192 200 208
  badTest_2048_block_24
  badTest_2048_block_25)
  (interval_append badTest_2048 208 216 224
  badTest_2048_block_26
  badTest_2048_block_27))
  (interval_append badTest_2048 224 240 256
  (interval_append badTest_2048 224 232 240
  badTest_2048_block_28
  badTest_2048_block_29)
  (interval_append badTest_2048 240 248 256
  badTest_2048_block_30
  badTest_2048_block_31)))))
cert_badTestInterval 2048 2304
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad009 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 2304
cert_badTest_block 2304 0 0 8 8
cert_badTest_block 2304 1 8 16 8
cert_badTest_block 2304 2 16 24 8
cert_badTest_block 2304 3 24 32 8
cert_badTest_block 2304 4 32 40 8
cert_badTest_block 2304 5 40 48 8
cert_badTest_block 2304 6 48 56 8
cert_badTest_block 2304 7 56 64 8
cert_badTest_block 2304 8 64 72 8
cert_badTest_block 2304 9 72 80 8
cert_badTest_block 2304 10 80 88 8
cert_badTest_block 2304 11 88 96 8
cert_badTest_block 2304 12 96 104 8
cert_badTest_block 2304 13 104 112 8
cert_badTest_block 2304 14 112 120 8
cert_badTest_block 2304 15 120 128 8
cert_badTest_block 2304 16 128 136 8
cert_badTest_block 2304 17 136 144 8
cert_badTest_block 2304 18 144 152 8
cert_badTest_block 2304 19 152 160 8
cert_badTest_block 2304 20 160 168 8
cert_badTest_block 2304 21 168 176 8
cert_badTest_block 2304 22 176 184 8
cert_badTest_block 2304 23 184 192 8
cert_badTest_block 2304 24 192 200 8
cert_badTest_block 2304 25 200 208 8
cert_badTest_block 2304 26 208 216 8
cert_badTest_block 2304 27 216 224 8
cert_badTest_block 2304 28 224 232 8
cert_badTest_block 2304 29 232 240 8
cert_badTest_block 2304 30 240 248 8
cert_badTest_block 2304 31 248 256 8
theorem badTest_2304_complete : Interval badTest_2304 0 256 :=
  (interval_append badTest_2304 0 128 256
  (interval_append badTest_2304 0 64 128
  (interval_append badTest_2304 0 32 64
  (interval_append badTest_2304 0 16 32
  (interval_append badTest_2304 0 8 16
  badTest_2304_block_0
  badTest_2304_block_1)
  (interval_append badTest_2304 16 24 32
  badTest_2304_block_2
  badTest_2304_block_3))
  (interval_append badTest_2304 32 48 64
  (interval_append badTest_2304 32 40 48
  badTest_2304_block_4
  badTest_2304_block_5)
  (interval_append badTest_2304 48 56 64
  badTest_2304_block_6
  badTest_2304_block_7)))
  (interval_append badTest_2304 64 96 128
  (interval_append badTest_2304 64 80 96
  (interval_append badTest_2304 64 72 80
  badTest_2304_block_8
  badTest_2304_block_9)
  (interval_append badTest_2304 80 88 96
  badTest_2304_block_10
  badTest_2304_block_11))
  (interval_append badTest_2304 96 112 128
  (interval_append badTest_2304 96 104 112
  badTest_2304_block_12
  badTest_2304_block_13)
  (interval_append badTest_2304 112 120 128
  badTest_2304_block_14
  badTest_2304_block_15))))
  (interval_append badTest_2304 128 192 256
  (interval_append badTest_2304 128 160 192
  (interval_append badTest_2304 128 144 160
  (interval_append badTest_2304 128 136 144
  badTest_2304_block_16
  badTest_2304_block_17)
  (interval_append badTest_2304 144 152 160
  badTest_2304_block_18
  badTest_2304_block_19))
  (interval_append badTest_2304 160 176 192
  (interval_append badTest_2304 160 168 176
  badTest_2304_block_20
  badTest_2304_block_21)
  (interval_append badTest_2304 176 184 192
  badTest_2304_block_22
  badTest_2304_block_23)))
  (interval_append badTest_2304 192 224 256
  (interval_append badTest_2304 192 208 224
  (interval_append badTest_2304 192 200 208
  badTest_2304_block_24
  badTest_2304_block_25)
  (interval_append badTest_2304 208 216 224
  badTest_2304_block_26
  badTest_2304_block_27))
  (interval_append badTest_2304 224 240 256
  (interval_append badTest_2304 224 232 240
  badTest_2304_block_28
  badTest_2304_block_29)
  (interval_append badTest_2304 240 248 256
  badTest_2304_block_30
  badTest_2304_block_31)))))
cert_badTestInterval 2304 2560
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad010 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 2560
cert_badTest_block 2560 0 0 8 8
cert_badTest_block 2560 1 8 16 8
cert_badTest_block 2560 2 16 24 8
cert_badTest_block 2560 3 24 32 8
cert_badTest_block 2560 4 32 40 8
cert_badTest_block 2560 5 40 48 8
cert_badTest_block 2560 6 48 56 8
cert_badTest_block 2560 7 56 64 8
cert_badTest_block 2560 8 64 72 8
cert_badTest_block 2560 9 72 80 8
cert_badTest_block 2560 10 80 88 8
cert_badTest_block 2560 11 88 96 8
cert_badTest_block 2560 12 96 104 8
cert_badTest_block 2560 13 104 112 8
cert_badTest_block 2560 14 112 120 8
cert_badTest_block 2560 15 120 128 8
cert_badTest_block 2560 16 128 136 8
cert_badTest_block 2560 17 136 144 8
cert_badTest_block 2560 18 144 152 8
cert_badTest_block 2560 19 152 160 8
cert_badTest_block 2560 20 160 168 8
cert_badTest_block 2560 21 168 176 8
cert_badTest_block 2560 22 176 184 8
cert_badTest_block 2560 23 184 192 8
cert_badTest_block 2560 24 192 200 8
cert_badTest_block 2560 25 200 208 8
cert_badTest_block 2560 26 208 216 8
cert_badTest_block 2560 27 216 224 8
cert_badTest_block 2560 28 224 232 8
cert_badTest_block 2560 29 232 240 8
cert_badTest_block 2560 30 240 248 8
cert_badTest_block 2560 31 248 256 8
theorem badTest_2560_complete : Interval badTest_2560 0 256 :=
  (interval_append badTest_2560 0 128 256
  (interval_append badTest_2560 0 64 128
  (interval_append badTest_2560 0 32 64
  (interval_append badTest_2560 0 16 32
  (interval_append badTest_2560 0 8 16
  badTest_2560_block_0
  badTest_2560_block_1)
  (interval_append badTest_2560 16 24 32
  badTest_2560_block_2
  badTest_2560_block_3))
  (interval_append badTest_2560 32 48 64
  (interval_append badTest_2560 32 40 48
  badTest_2560_block_4
  badTest_2560_block_5)
  (interval_append badTest_2560 48 56 64
  badTest_2560_block_6
  badTest_2560_block_7)))
  (interval_append badTest_2560 64 96 128
  (interval_append badTest_2560 64 80 96
  (interval_append badTest_2560 64 72 80
  badTest_2560_block_8
  badTest_2560_block_9)
  (interval_append badTest_2560 80 88 96
  badTest_2560_block_10
  badTest_2560_block_11))
  (interval_append badTest_2560 96 112 128
  (interval_append badTest_2560 96 104 112
  badTest_2560_block_12
  badTest_2560_block_13)
  (interval_append badTest_2560 112 120 128
  badTest_2560_block_14
  badTest_2560_block_15))))
  (interval_append badTest_2560 128 192 256
  (interval_append badTest_2560 128 160 192
  (interval_append badTest_2560 128 144 160
  (interval_append badTest_2560 128 136 144
  badTest_2560_block_16
  badTest_2560_block_17)
  (interval_append badTest_2560 144 152 160
  badTest_2560_block_18
  badTest_2560_block_19))
  (interval_append badTest_2560 160 176 192
  (interval_append badTest_2560 160 168 176
  badTest_2560_block_20
  badTest_2560_block_21)
  (interval_append badTest_2560 176 184 192
  badTest_2560_block_22
  badTest_2560_block_23)))
  (interval_append badTest_2560 192 224 256
  (interval_append badTest_2560 192 208 224
  (interval_append badTest_2560 192 200 208
  badTest_2560_block_24
  badTest_2560_block_25)
  (interval_append badTest_2560 208 216 224
  badTest_2560_block_26
  badTest_2560_block_27))
  (interval_append badTest_2560 224 240 256
  (interval_append badTest_2560 224 232 240
  badTest_2560_block_28
  badTest_2560_block_29)
  (interval_append badTest_2560 240 248 256
  badTest_2560_block_30
  badTest_2560_block_31)))))
cert_badTestInterval 2560 2816
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad011 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 2816
cert_badTest_block 2816 0 0 8 8
cert_badTest_block 2816 1 8 16 8
cert_badTest_block 2816 2 16 24 8
cert_badTest_block 2816 3 24 32 8
cert_badTest_block 2816 4 32 40 8
cert_badTest_block 2816 5 40 48 8
cert_badTest_block 2816 6 48 56 8
cert_badTest_block 2816 7 56 64 8
cert_badTest_block 2816 8 64 72 8
cert_badTest_block 2816 9 72 80 8
cert_badTest_block 2816 10 80 88 8
cert_badTest_block 2816 11 88 96 8
cert_badTest_block 2816 12 96 104 8
cert_badTest_block 2816 13 104 112 8
cert_badTest_block 2816 14 112 120 8
cert_badTest_block 2816 15 120 128 8
cert_badTest_block 2816 16 128 136 8
cert_badTest_block 2816 17 136 144 8
cert_badTest_block 2816 18 144 152 8
cert_badTest_block 2816 19 152 160 8
cert_badTest_block 2816 20 160 168 8
cert_badTest_block 2816 21 168 176 8
cert_badTest_block 2816 22 176 184 8
cert_badTest_block 2816 23 184 192 8
cert_badTest_block 2816 24 192 200 8
cert_badTest_block 2816 25 200 208 8
cert_badTest_block 2816 26 208 216 8
cert_badTest_block 2816 27 216 224 8
cert_badTest_block 2816 28 224 232 8
cert_badTest_block 2816 29 232 240 8
cert_badTest_block 2816 30 240 248 8
cert_badTest_block 2816 31 248 256 8
theorem badTest_2816_complete : Interval badTest_2816 0 256 :=
  (interval_append badTest_2816 0 128 256
  (interval_append badTest_2816 0 64 128
  (interval_append badTest_2816 0 32 64
  (interval_append badTest_2816 0 16 32
  (interval_append badTest_2816 0 8 16
  badTest_2816_block_0
  badTest_2816_block_1)
  (interval_append badTest_2816 16 24 32
  badTest_2816_block_2
  badTest_2816_block_3))
  (interval_append badTest_2816 32 48 64
  (interval_append badTest_2816 32 40 48
  badTest_2816_block_4
  badTest_2816_block_5)
  (interval_append badTest_2816 48 56 64
  badTest_2816_block_6
  badTest_2816_block_7)))
  (interval_append badTest_2816 64 96 128
  (interval_append badTest_2816 64 80 96
  (interval_append badTest_2816 64 72 80
  badTest_2816_block_8
  badTest_2816_block_9)
  (interval_append badTest_2816 80 88 96
  badTest_2816_block_10
  badTest_2816_block_11))
  (interval_append badTest_2816 96 112 128
  (interval_append badTest_2816 96 104 112
  badTest_2816_block_12
  badTest_2816_block_13)
  (interval_append badTest_2816 112 120 128
  badTest_2816_block_14
  badTest_2816_block_15))))
  (interval_append badTest_2816 128 192 256
  (interval_append badTest_2816 128 160 192
  (interval_append badTest_2816 128 144 160
  (interval_append badTest_2816 128 136 144
  badTest_2816_block_16
  badTest_2816_block_17)
  (interval_append badTest_2816 144 152 160
  badTest_2816_block_18
  badTest_2816_block_19))
  (interval_append badTest_2816 160 176 192
  (interval_append badTest_2816 160 168 176
  badTest_2816_block_20
  badTest_2816_block_21)
  (interval_append badTest_2816 176 184 192
  badTest_2816_block_22
  badTest_2816_block_23)))
  (interval_append badTest_2816 192 224 256
  (interval_append badTest_2816 192 208 224
  (interval_append badTest_2816 192 200 208
  badTest_2816_block_24
  badTest_2816_block_25)
  (interval_append badTest_2816 208 216 224
  badTest_2816_block_26
  badTest_2816_block_27))
  (interval_append badTest_2816 224 240 256
  (interval_append badTest_2816 224 232 240
  badTest_2816_block_28
  badTest_2816_block_29)
  (interval_append badTest_2816 240 248 256
  badTest_2816_block_30
  badTest_2816_block_31)))))
cert_badTestInterval 2816 3072
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad012 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 3072
cert_badTest_block 3072 0 0 8 8
cert_badTest_block 3072 1 8 16 8
cert_badTest_block 3072 2 16 24 8
cert_badTest_block 3072 3 24 32 8
cert_badTest_block 3072 4 32 40 8
cert_badTest_block 3072 5 40 48 8
cert_badTest_block 3072 6 48 56 8
cert_badTest_block 3072 7 56 64 8
cert_badTest_block 3072 8 64 72 8
cert_badTest_block 3072 9 72 80 8
cert_badTest_block 3072 10 80 88 8
cert_badTest_block 3072 11 88 96 8
cert_badTest_block 3072 12 96 104 8
cert_badTest_block 3072 13 104 112 8
cert_badTest_block 3072 14 112 120 8
cert_badTest_block 3072 15 120 128 8
cert_badTest_block 3072 16 128 136 8
cert_badTest_block 3072 17 136 144 8
cert_badTest_block 3072 18 144 152 8
cert_badTest_block 3072 19 152 160 8
cert_badTest_block 3072 20 160 168 8
cert_badTest_block 3072 21 168 176 8
cert_badTest_block 3072 22 176 184 8
cert_badTest_block 3072 23 184 192 8
cert_badTest_block 3072 24 192 200 8
cert_badTest_block 3072 25 200 208 8
cert_badTest_block 3072 26 208 216 8
cert_badTest_block 3072 27 216 224 8
cert_badTest_block 3072 28 224 232 8
cert_badTest_block 3072 29 232 240 8
cert_badTest_block 3072 30 240 248 8
cert_badTest_block 3072 31 248 256 8
theorem badTest_3072_complete : Interval badTest_3072 0 256 :=
  (interval_append badTest_3072 0 128 256
  (interval_append badTest_3072 0 64 128
  (interval_append badTest_3072 0 32 64
  (interval_append badTest_3072 0 16 32
  (interval_append badTest_3072 0 8 16
  badTest_3072_block_0
  badTest_3072_block_1)
  (interval_append badTest_3072 16 24 32
  badTest_3072_block_2
  badTest_3072_block_3))
  (interval_append badTest_3072 32 48 64
  (interval_append badTest_3072 32 40 48
  badTest_3072_block_4
  badTest_3072_block_5)
  (interval_append badTest_3072 48 56 64
  badTest_3072_block_6
  badTest_3072_block_7)))
  (interval_append badTest_3072 64 96 128
  (interval_append badTest_3072 64 80 96
  (interval_append badTest_3072 64 72 80
  badTest_3072_block_8
  badTest_3072_block_9)
  (interval_append badTest_3072 80 88 96
  badTest_3072_block_10
  badTest_3072_block_11))
  (interval_append badTest_3072 96 112 128
  (interval_append badTest_3072 96 104 112
  badTest_3072_block_12
  badTest_3072_block_13)
  (interval_append badTest_3072 112 120 128
  badTest_3072_block_14
  badTest_3072_block_15))))
  (interval_append badTest_3072 128 192 256
  (interval_append badTest_3072 128 160 192
  (interval_append badTest_3072 128 144 160
  (interval_append badTest_3072 128 136 144
  badTest_3072_block_16
  badTest_3072_block_17)
  (interval_append badTest_3072 144 152 160
  badTest_3072_block_18
  badTest_3072_block_19))
  (interval_append badTest_3072 160 176 192
  (interval_append badTest_3072 160 168 176
  badTest_3072_block_20
  badTest_3072_block_21)
  (interval_append badTest_3072 176 184 192
  badTest_3072_block_22
  badTest_3072_block_23)))
  (interval_append badTest_3072 192 224 256
  (interval_append badTest_3072 192 208 224
  (interval_append badTest_3072 192 200 208
  badTest_3072_block_24
  badTest_3072_block_25)
  (interval_append badTest_3072 208 216 224
  badTest_3072_block_26
  badTest_3072_block_27))
  (interval_append badTest_3072 224 240 256
  (interval_append badTest_3072 224 232 240
  badTest_3072_block_28
  badTest_3072_block_29)
  (interval_append badTest_3072 240 248 256
  badTest_3072_block_30
  badTest_3072_block_31)))))
cert_badTestInterval 3072 3328
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad013 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 3328
cert_badTest_block 3328 0 0 8 8
cert_badTest_block 3328 1 8 16 8
cert_badTest_block 3328 2 16 24 8
cert_badTest_block 3328 3 24 32 8
cert_badTest_block 3328 4 32 40 8
cert_badTest_block 3328 5 40 48 8
cert_badTest_block 3328 6 48 56 8
cert_badTest_block 3328 7 56 64 8
cert_badTest_block 3328 8 64 72 8
cert_badTest_block 3328 9 72 80 8
cert_badTest_block 3328 10 80 88 8
cert_badTest_block 3328 11 88 96 8
cert_badTest_block 3328 12 96 104 8
cert_badTest_block 3328 13 104 112 8
cert_badTest_block 3328 14 112 120 8
cert_badTest_block 3328 15 120 128 8
cert_badTest_block 3328 16 128 136 8
cert_badTest_block 3328 17 136 144 8
cert_badTest_block 3328 18 144 152 8
cert_badTest_block 3328 19 152 160 8
cert_badTest_block 3328 20 160 168 8
cert_badTest_block 3328 21 168 176 8
cert_badTest_block 3328 22 176 184 8
cert_badTest_block 3328 23 184 192 8
cert_badTest_block 3328 24 192 200 8
cert_badTest_block 3328 25 200 208 8
cert_badTest_block 3328 26 208 216 8
cert_badTest_block 3328 27 216 224 8
cert_badTest_block 3328 28 224 232 8
cert_badTest_block 3328 29 232 240 8
cert_badTest_block 3328 30 240 248 8
cert_badTest_block 3328 31 248 256 8
theorem badTest_3328_complete : Interval badTest_3328 0 256 :=
  (interval_append badTest_3328 0 128 256
  (interval_append badTest_3328 0 64 128
  (interval_append badTest_3328 0 32 64
  (interval_append badTest_3328 0 16 32
  (interval_append badTest_3328 0 8 16
  badTest_3328_block_0
  badTest_3328_block_1)
  (interval_append badTest_3328 16 24 32
  badTest_3328_block_2
  badTest_3328_block_3))
  (interval_append badTest_3328 32 48 64
  (interval_append badTest_3328 32 40 48
  badTest_3328_block_4
  badTest_3328_block_5)
  (interval_append badTest_3328 48 56 64
  badTest_3328_block_6
  badTest_3328_block_7)))
  (interval_append badTest_3328 64 96 128
  (interval_append badTest_3328 64 80 96
  (interval_append badTest_3328 64 72 80
  badTest_3328_block_8
  badTest_3328_block_9)
  (interval_append badTest_3328 80 88 96
  badTest_3328_block_10
  badTest_3328_block_11))
  (interval_append badTest_3328 96 112 128
  (interval_append badTest_3328 96 104 112
  badTest_3328_block_12
  badTest_3328_block_13)
  (interval_append badTest_3328 112 120 128
  badTest_3328_block_14
  badTest_3328_block_15))))
  (interval_append badTest_3328 128 192 256
  (interval_append badTest_3328 128 160 192
  (interval_append badTest_3328 128 144 160
  (interval_append badTest_3328 128 136 144
  badTest_3328_block_16
  badTest_3328_block_17)
  (interval_append badTest_3328 144 152 160
  badTest_3328_block_18
  badTest_3328_block_19))
  (interval_append badTest_3328 160 176 192
  (interval_append badTest_3328 160 168 176
  badTest_3328_block_20
  badTest_3328_block_21)
  (interval_append badTest_3328 176 184 192
  badTest_3328_block_22
  badTest_3328_block_23)))
  (interval_append badTest_3328 192 224 256
  (interval_append badTest_3328 192 208 224
  (interval_append badTest_3328 192 200 208
  badTest_3328_block_24
  badTest_3328_block_25)
  (interval_append badTest_3328 208 216 224
  badTest_3328_block_26
  badTest_3328_block_27))
  (interval_append badTest_3328 224 240 256
  (interval_append badTest_3328 224 232 240
  badTest_3328_block_28
  badTest_3328_block_29)
  (interval_append badTest_3328 240 248 256
  badTest_3328_block_30
  badTest_3328_block_31)))))
cert_badTestInterval 3328 3584
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad014 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 3584
cert_badTest_block 3584 0 0 8 8
cert_badTest_block 3584 1 8 16 8
cert_badTest_block 3584 2 16 24 8
cert_badTest_block 3584 3 24 32 8
cert_badTest_block 3584 4 32 40 8
cert_badTest_block 3584 5 40 48 8
cert_badTest_block 3584 6 48 56 8
cert_badTest_block 3584 7 56 64 8
cert_badTest_block 3584 8 64 72 8
cert_badTest_block 3584 9 72 80 8
cert_badTest_block 3584 10 80 88 8
cert_badTest_block 3584 11 88 96 8
cert_badTest_block 3584 12 96 104 8
cert_badTest_block 3584 13 104 112 8
cert_badTest_block 3584 14 112 120 8
cert_badTest_block 3584 15 120 128 8
cert_badTest_block 3584 16 128 136 8
cert_badTest_block 3584 17 136 144 8
cert_badTest_block 3584 18 144 152 8
cert_badTest_block 3584 19 152 160 8
cert_badTest_block 3584 20 160 168 8
cert_badTest_block 3584 21 168 176 8
cert_badTest_block 3584 22 176 184 8
cert_badTest_block 3584 23 184 192 8
cert_badTest_block 3584 24 192 200 8
cert_badTest_block 3584 25 200 208 8
cert_badTest_block 3584 26 208 216 8
cert_badTest_block 3584 27 216 224 8
cert_badTest_block 3584 28 224 232 8
cert_badTest_block 3584 29 232 240 8
cert_badTest_block 3584 30 240 248 8
cert_badTest_block 3584 31 248 256 8
theorem badTest_3584_complete : Interval badTest_3584 0 256 :=
  (interval_append badTest_3584 0 128 256
  (interval_append badTest_3584 0 64 128
  (interval_append badTest_3584 0 32 64
  (interval_append badTest_3584 0 16 32
  (interval_append badTest_3584 0 8 16
  badTest_3584_block_0
  badTest_3584_block_1)
  (interval_append badTest_3584 16 24 32
  badTest_3584_block_2
  badTest_3584_block_3))
  (interval_append badTest_3584 32 48 64
  (interval_append badTest_3584 32 40 48
  badTest_3584_block_4
  badTest_3584_block_5)
  (interval_append badTest_3584 48 56 64
  badTest_3584_block_6
  badTest_3584_block_7)))
  (interval_append badTest_3584 64 96 128
  (interval_append badTest_3584 64 80 96
  (interval_append badTest_3584 64 72 80
  badTest_3584_block_8
  badTest_3584_block_9)
  (interval_append badTest_3584 80 88 96
  badTest_3584_block_10
  badTest_3584_block_11))
  (interval_append badTest_3584 96 112 128
  (interval_append badTest_3584 96 104 112
  badTest_3584_block_12
  badTest_3584_block_13)
  (interval_append badTest_3584 112 120 128
  badTest_3584_block_14
  badTest_3584_block_15))))
  (interval_append badTest_3584 128 192 256
  (interval_append badTest_3584 128 160 192
  (interval_append badTest_3584 128 144 160
  (interval_append badTest_3584 128 136 144
  badTest_3584_block_16
  badTest_3584_block_17)
  (interval_append badTest_3584 144 152 160
  badTest_3584_block_18
  badTest_3584_block_19))
  (interval_append badTest_3584 160 176 192
  (interval_append badTest_3584 160 168 176
  badTest_3584_block_20
  badTest_3584_block_21)
  (interval_append badTest_3584 176 184 192
  badTest_3584_block_22
  badTest_3584_block_23)))
  (interval_append badTest_3584 192 224 256
  (interval_append badTest_3584 192 208 224
  (interval_append badTest_3584 192 200 208
  badTest_3584_block_24
  badTest_3584_block_25)
  (interval_append badTest_3584 208 216 224
  badTest_3584_block_26
  badTest_3584_block_27))
  (interval_append badTest_3584 224 240 256
  (interval_append badTest_3584 224 232 240
  badTest_3584_block_28
  badTest_3584_block_29)
  (interval_append badTest_3584 240 248 256
  badTest_3584_block_30
  badTest_3584_block_31)))))
cert_badTestInterval 3584 3840
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad015 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 3840
cert_badTest_block 3840 0 0 8 8
cert_badTest_block 3840 1 8 16 8
cert_badTest_block 3840 2 16 24 8
cert_badTest_block 3840 3 24 32 8
cert_badTest_block 3840 4 32 40 8
cert_badTest_block 3840 5 40 48 8
cert_badTest_block 3840 6 48 56 8
cert_badTest_block 3840 7 56 64 8
cert_badTest_block 3840 8 64 72 8
cert_badTest_block 3840 9 72 80 8
cert_badTest_block 3840 10 80 88 8
cert_badTest_block 3840 11 88 96 8
cert_badTest_block 3840 12 96 104 8
cert_badTest_block 3840 13 104 112 8
cert_badTest_block 3840 14 112 120 8
cert_badTest_block 3840 15 120 128 8
cert_badTest_block 3840 16 128 136 8
cert_badTest_block 3840 17 136 144 8
cert_badTest_block 3840 18 144 152 8
cert_badTest_block 3840 19 152 160 8
cert_badTest_block 3840 20 160 168 8
cert_badTest_block 3840 21 168 176 8
cert_badTest_block 3840 22 176 184 8
cert_badTest_block 3840 23 184 192 8
cert_badTest_block 3840 24 192 200 8
cert_badTest_block 3840 25 200 208 8
cert_badTest_block 3840 26 208 216 8
cert_badTest_block 3840 27 216 224 8
cert_badTest_block 3840 28 224 232 8
cert_badTest_block 3840 29 232 240 8
cert_badTest_block 3840 30 240 248 8
cert_badTest_block 3840 31 248 256 8
theorem badTest_3840_complete : Interval badTest_3840 0 256 :=
  (interval_append badTest_3840 0 128 256
  (interval_append badTest_3840 0 64 128
  (interval_append badTest_3840 0 32 64
  (interval_append badTest_3840 0 16 32
  (interval_append badTest_3840 0 8 16
  badTest_3840_block_0
  badTest_3840_block_1)
  (interval_append badTest_3840 16 24 32
  badTest_3840_block_2
  badTest_3840_block_3))
  (interval_append badTest_3840 32 48 64
  (interval_append badTest_3840 32 40 48
  badTest_3840_block_4
  badTest_3840_block_5)
  (interval_append badTest_3840 48 56 64
  badTest_3840_block_6
  badTest_3840_block_7)))
  (interval_append badTest_3840 64 96 128
  (interval_append badTest_3840 64 80 96
  (interval_append badTest_3840 64 72 80
  badTest_3840_block_8
  badTest_3840_block_9)
  (interval_append badTest_3840 80 88 96
  badTest_3840_block_10
  badTest_3840_block_11))
  (interval_append badTest_3840 96 112 128
  (interval_append badTest_3840 96 104 112
  badTest_3840_block_12
  badTest_3840_block_13)
  (interval_append badTest_3840 112 120 128
  badTest_3840_block_14
  badTest_3840_block_15))))
  (interval_append badTest_3840 128 192 256
  (interval_append badTest_3840 128 160 192
  (interval_append badTest_3840 128 144 160
  (interval_append badTest_3840 128 136 144
  badTest_3840_block_16
  badTest_3840_block_17)
  (interval_append badTest_3840 144 152 160
  badTest_3840_block_18
  badTest_3840_block_19))
  (interval_append badTest_3840 160 176 192
  (interval_append badTest_3840 160 168 176
  badTest_3840_block_20
  badTest_3840_block_21)
  (interval_append badTest_3840 176 184 192
  badTest_3840_block_22
  badTest_3840_block_23)))
  (interval_append badTest_3840 192 224 256
  (interval_append badTest_3840 192 208 224
  (interval_append badTest_3840 192 200 208
  badTest_3840_block_24
  badTest_3840_block_25)
  (interval_append badTest_3840 208 216 224
  badTest_3840_block_26
  badTest_3840_block_27))
  (interval_append badTest_3840 224 240 256
  (interval_append badTest_3840 224 232 240
  badTest_3840_block_28
  badTest_3840_block_29)
  (interval_append badTest_3840 240 248 256
  badTest_3840_block_30
  badTest_3840_block_31)))))
cert_badTestInterval 3840 4096
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad016 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 4096
cert_badTest_block 4096 0 0 8 8
cert_badTest_block 4096 1 8 16 8
cert_badTest_block 4096 2 16 24 8
cert_badTest_block 4096 3 24 32 8
cert_badTest_block 4096 4 32 40 8
cert_badTest_block 4096 5 40 48 8
cert_badTest_block 4096 6 48 56 8
cert_badTest_block 4096 7 56 64 8
cert_badTest_block 4096 8 64 72 8
cert_badTest_block 4096 9 72 80 8
cert_badTest_block 4096 10 80 88 8
cert_badTest_block 4096 11 88 96 8
cert_badTest_block 4096 12 96 104 8
cert_badTest_block 4096 13 104 112 8
cert_badTest_block 4096 14 112 120 8
cert_badTest_block 4096 15 120 128 8
cert_badTest_block 4096 16 128 136 8
cert_badTest_block 4096 17 136 144 8
cert_badTest_block 4096 18 144 152 8
cert_badTest_block 4096 19 152 160 8
cert_badTest_block 4096 20 160 168 8
cert_badTest_block 4096 21 168 176 8
cert_badTest_block 4096 22 176 184 8
cert_badTest_block 4096 23 184 192 8
cert_badTest_block 4096 24 192 200 8
cert_badTest_block 4096 25 200 208 8
cert_badTest_block 4096 26 208 216 8
cert_badTest_block 4096 27 216 224 8
cert_badTest_block 4096 28 224 232 8
cert_badTest_block 4096 29 232 240 8
cert_badTest_block 4096 30 240 248 8
cert_badTest_block 4096 31 248 256 8
theorem badTest_4096_complete : Interval badTest_4096 0 256 :=
  (interval_append badTest_4096 0 128 256
  (interval_append badTest_4096 0 64 128
  (interval_append badTest_4096 0 32 64
  (interval_append badTest_4096 0 16 32
  (interval_append badTest_4096 0 8 16
  badTest_4096_block_0
  badTest_4096_block_1)
  (interval_append badTest_4096 16 24 32
  badTest_4096_block_2
  badTest_4096_block_3))
  (interval_append badTest_4096 32 48 64
  (interval_append badTest_4096 32 40 48
  badTest_4096_block_4
  badTest_4096_block_5)
  (interval_append badTest_4096 48 56 64
  badTest_4096_block_6
  badTest_4096_block_7)))
  (interval_append badTest_4096 64 96 128
  (interval_append badTest_4096 64 80 96
  (interval_append badTest_4096 64 72 80
  badTest_4096_block_8
  badTest_4096_block_9)
  (interval_append badTest_4096 80 88 96
  badTest_4096_block_10
  badTest_4096_block_11))
  (interval_append badTest_4096 96 112 128
  (interval_append badTest_4096 96 104 112
  badTest_4096_block_12
  badTest_4096_block_13)
  (interval_append badTest_4096 112 120 128
  badTest_4096_block_14
  badTest_4096_block_15))))
  (interval_append badTest_4096 128 192 256
  (interval_append badTest_4096 128 160 192
  (interval_append badTest_4096 128 144 160
  (interval_append badTest_4096 128 136 144
  badTest_4096_block_16
  badTest_4096_block_17)
  (interval_append badTest_4096 144 152 160
  badTest_4096_block_18
  badTest_4096_block_19))
  (interval_append badTest_4096 160 176 192
  (interval_append badTest_4096 160 168 176
  badTest_4096_block_20
  badTest_4096_block_21)
  (interval_append badTest_4096 176 184 192
  badTest_4096_block_22
  badTest_4096_block_23)))
  (interval_append badTest_4096 192 224 256
  (interval_append badTest_4096 192 208 224
  (interval_append badTest_4096 192 200 208
  badTest_4096_block_24
  badTest_4096_block_25)
  (interval_append badTest_4096 208 216 224
  badTest_4096_block_26
  badTest_4096_block_27))
  (interval_append badTest_4096 224 240 256
  (interval_append badTest_4096 224 232 240
  badTest_4096_block_28
  badTest_4096_block_29)
  (interval_append badTest_4096 240 248 256
  badTest_4096_block_30
  badTest_4096_block_31)))))
cert_badTestInterval 4096 4352
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad017 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 4352
cert_badTest_block 4352 0 0 8 8
cert_badTest_block 4352 1 8 16 8
cert_badTest_block 4352 2 16 24 8
cert_badTest_block 4352 3 24 32 8
cert_badTest_block 4352 4 32 40 8
cert_badTest_block 4352 5 40 48 8
cert_badTest_block 4352 6 48 56 8
cert_badTest_block 4352 7 56 64 8
cert_badTest_block 4352 8 64 72 8
cert_badTest_block 4352 9 72 80 8
cert_badTest_block 4352 10 80 88 8
cert_badTest_block 4352 11 88 96 8
cert_badTest_block 4352 12 96 104 8
cert_badTest_block 4352 13 104 112 8
cert_badTest_block 4352 14 112 120 8
cert_badTest_block 4352 15 120 128 8
cert_badTest_block 4352 16 128 136 8
cert_badTest_block 4352 17 136 144 8
cert_badTest_block 4352 18 144 152 8
cert_badTest_block 4352 19 152 160 8
cert_badTest_block 4352 20 160 168 8
cert_badTest_block 4352 21 168 176 8
cert_badTest_block 4352 22 176 184 8
cert_badTest_block 4352 23 184 192 8
cert_badTest_block 4352 24 192 200 8
cert_badTest_block 4352 25 200 208 8
cert_badTest_block 4352 26 208 216 8
cert_badTest_block 4352 27 216 224 8
cert_badTest_block 4352 28 224 232 8
cert_badTest_block 4352 29 232 240 8
cert_badTest_block 4352 30 240 248 8
cert_badTest_block 4352 31 248 256 8
theorem badTest_4352_complete : Interval badTest_4352 0 256 :=
  (interval_append badTest_4352 0 128 256
  (interval_append badTest_4352 0 64 128
  (interval_append badTest_4352 0 32 64
  (interval_append badTest_4352 0 16 32
  (interval_append badTest_4352 0 8 16
  badTest_4352_block_0
  badTest_4352_block_1)
  (interval_append badTest_4352 16 24 32
  badTest_4352_block_2
  badTest_4352_block_3))
  (interval_append badTest_4352 32 48 64
  (interval_append badTest_4352 32 40 48
  badTest_4352_block_4
  badTest_4352_block_5)
  (interval_append badTest_4352 48 56 64
  badTest_4352_block_6
  badTest_4352_block_7)))
  (interval_append badTest_4352 64 96 128
  (interval_append badTest_4352 64 80 96
  (interval_append badTest_4352 64 72 80
  badTest_4352_block_8
  badTest_4352_block_9)
  (interval_append badTest_4352 80 88 96
  badTest_4352_block_10
  badTest_4352_block_11))
  (interval_append badTest_4352 96 112 128
  (interval_append badTest_4352 96 104 112
  badTest_4352_block_12
  badTest_4352_block_13)
  (interval_append badTest_4352 112 120 128
  badTest_4352_block_14
  badTest_4352_block_15))))
  (interval_append badTest_4352 128 192 256
  (interval_append badTest_4352 128 160 192
  (interval_append badTest_4352 128 144 160
  (interval_append badTest_4352 128 136 144
  badTest_4352_block_16
  badTest_4352_block_17)
  (interval_append badTest_4352 144 152 160
  badTest_4352_block_18
  badTest_4352_block_19))
  (interval_append badTest_4352 160 176 192
  (interval_append badTest_4352 160 168 176
  badTest_4352_block_20
  badTest_4352_block_21)
  (interval_append badTest_4352 176 184 192
  badTest_4352_block_22
  badTest_4352_block_23)))
  (interval_append badTest_4352 192 224 256
  (interval_append badTest_4352 192 208 224
  (interval_append badTest_4352 192 200 208
  badTest_4352_block_24
  badTest_4352_block_25)
  (interval_append badTest_4352 208 216 224
  badTest_4352_block_26
  badTest_4352_block_27))
  (interval_append badTest_4352 224 240 256
  (interval_append badTest_4352 224 232 240
  badTest_4352_block_28
  badTest_4352_block_29)
  (interval_append badTest_4352 240 248 256
  badTest_4352_block_30
  badTest_4352_block_31)))))
cert_badTestInterval 4352 4608
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad018 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 4608
cert_badTest_block 4608 0 0 8 8
cert_badTest_block 4608 1 8 16 8
cert_badTest_block 4608 2 16 24 8
cert_badTest_block 4608 3 24 32 8
cert_badTest_block 4608 4 32 40 8
cert_badTest_block 4608 5 40 48 8
cert_badTest_block 4608 6 48 56 8
cert_badTest_block 4608 7 56 64 8
cert_badTest_block 4608 8 64 72 8
cert_badTest_block 4608 9 72 80 8
cert_badTest_block 4608 10 80 88 8
cert_badTest_block 4608 11 88 96 8
cert_badTest_block 4608 12 96 104 8
cert_badTest_block 4608 13 104 112 8
cert_badTest_block 4608 14 112 120 8
cert_badTest_block 4608 15 120 128 8
cert_badTest_block 4608 16 128 136 8
cert_badTest_block 4608 17 136 144 8
cert_badTest_block 4608 18 144 152 8
cert_badTest_block 4608 19 152 160 8
cert_badTest_block 4608 20 160 168 8
cert_badTest_block 4608 21 168 176 8
cert_badTest_block 4608 22 176 184 8
cert_badTest_block 4608 23 184 192 8
cert_badTest_block 4608 24 192 200 8
cert_badTest_block 4608 25 200 208 8
cert_badTest_block 4608 26 208 216 8
cert_badTest_block 4608 27 216 224 8
cert_badTest_block 4608 28 224 232 8
cert_badTest_block 4608 29 232 240 8
cert_badTest_block 4608 30 240 248 8
cert_badTest_block 4608 31 248 256 8
theorem badTest_4608_complete : Interval badTest_4608 0 256 :=
  (interval_append badTest_4608 0 128 256
  (interval_append badTest_4608 0 64 128
  (interval_append badTest_4608 0 32 64
  (interval_append badTest_4608 0 16 32
  (interval_append badTest_4608 0 8 16
  badTest_4608_block_0
  badTest_4608_block_1)
  (interval_append badTest_4608 16 24 32
  badTest_4608_block_2
  badTest_4608_block_3))
  (interval_append badTest_4608 32 48 64
  (interval_append badTest_4608 32 40 48
  badTest_4608_block_4
  badTest_4608_block_5)
  (interval_append badTest_4608 48 56 64
  badTest_4608_block_6
  badTest_4608_block_7)))
  (interval_append badTest_4608 64 96 128
  (interval_append badTest_4608 64 80 96
  (interval_append badTest_4608 64 72 80
  badTest_4608_block_8
  badTest_4608_block_9)
  (interval_append badTest_4608 80 88 96
  badTest_4608_block_10
  badTest_4608_block_11))
  (interval_append badTest_4608 96 112 128
  (interval_append badTest_4608 96 104 112
  badTest_4608_block_12
  badTest_4608_block_13)
  (interval_append badTest_4608 112 120 128
  badTest_4608_block_14
  badTest_4608_block_15))))
  (interval_append badTest_4608 128 192 256
  (interval_append badTest_4608 128 160 192
  (interval_append badTest_4608 128 144 160
  (interval_append badTest_4608 128 136 144
  badTest_4608_block_16
  badTest_4608_block_17)
  (interval_append badTest_4608 144 152 160
  badTest_4608_block_18
  badTest_4608_block_19))
  (interval_append badTest_4608 160 176 192
  (interval_append badTest_4608 160 168 176
  badTest_4608_block_20
  badTest_4608_block_21)
  (interval_append badTest_4608 176 184 192
  badTest_4608_block_22
  badTest_4608_block_23)))
  (interval_append badTest_4608 192 224 256
  (interval_append badTest_4608 192 208 224
  (interval_append badTest_4608 192 200 208
  badTest_4608_block_24
  badTest_4608_block_25)
  (interval_append badTest_4608 208 216 224
  badTest_4608_block_26
  badTest_4608_block_27))
  (interval_append badTest_4608 224 240 256
  (interval_append badTest_4608 224 232 240
  badTest_4608_block_28
  badTest_4608_block_29)
  (interval_append badTest_4608 240 248 256
  badTest_4608_block_30
  badTest_4608_block_31)))))
cert_badTestInterval 4608 4864
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad019 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 4864
cert_badTest_block 4864 0 0 8 8
cert_badTest_block 4864 1 8 16 8
cert_badTest_block 4864 2 16 24 8
cert_badTest_block 4864 3 24 32 8
cert_badTest_block 4864 4 32 40 8
cert_badTest_block 4864 5 40 48 8
cert_badTest_block 4864 6 48 56 8
cert_badTest_block 4864 7 56 64 8
cert_badTest_block 4864 8 64 72 8
cert_badTest_block 4864 9 72 80 8
cert_badTest_block 4864 10 80 88 8
cert_badTest_block 4864 11 88 96 8
cert_badTest_block 4864 12 96 104 8
cert_badTest_block 4864 13 104 112 8
cert_badTest_block 4864 14 112 120 8
cert_badTest_block 4864 15 120 128 8
cert_badTest_block 4864 16 128 136 8
cert_badTest_block 4864 17 136 144 8
cert_badTest_block 4864 18 144 152 8
cert_badTest_block 4864 19 152 160 8
cert_badTest_block 4864 20 160 168 8
cert_badTest_block 4864 21 168 176 8
cert_badTest_block 4864 22 176 184 8
cert_badTest_block 4864 23 184 192 8
cert_badTest_block 4864 24 192 200 8
cert_badTest_block 4864 25 200 208 8
cert_badTest_block 4864 26 208 216 8
cert_badTest_block 4864 27 216 224 8
cert_badTest_block 4864 28 224 232 8
cert_badTest_block 4864 29 232 240 8
cert_badTest_block 4864 30 240 248 8
cert_badTest_block 4864 31 248 256 8
theorem badTest_4864_complete : Interval badTest_4864 0 256 :=
  (interval_append badTest_4864 0 128 256
  (interval_append badTest_4864 0 64 128
  (interval_append badTest_4864 0 32 64
  (interval_append badTest_4864 0 16 32
  (interval_append badTest_4864 0 8 16
  badTest_4864_block_0
  badTest_4864_block_1)
  (interval_append badTest_4864 16 24 32
  badTest_4864_block_2
  badTest_4864_block_3))
  (interval_append badTest_4864 32 48 64
  (interval_append badTest_4864 32 40 48
  badTest_4864_block_4
  badTest_4864_block_5)
  (interval_append badTest_4864 48 56 64
  badTest_4864_block_6
  badTest_4864_block_7)))
  (interval_append badTest_4864 64 96 128
  (interval_append badTest_4864 64 80 96
  (interval_append badTest_4864 64 72 80
  badTest_4864_block_8
  badTest_4864_block_9)
  (interval_append badTest_4864 80 88 96
  badTest_4864_block_10
  badTest_4864_block_11))
  (interval_append badTest_4864 96 112 128
  (interval_append badTest_4864 96 104 112
  badTest_4864_block_12
  badTest_4864_block_13)
  (interval_append badTest_4864 112 120 128
  badTest_4864_block_14
  badTest_4864_block_15))))
  (interval_append badTest_4864 128 192 256
  (interval_append badTest_4864 128 160 192
  (interval_append badTest_4864 128 144 160
  (interval_append badTest_4864 128 136 144
  badTest_4864_block_16
  badTest_4864_block_17)
  (interval_append badTest_4864 144 152 160
  badTest_4864_block_18
  badTest_4864_block_19))
  (interval_append badTest_4864 160 176 192
  (interval_append badTest_4864 160 168 176
  badTest_4864_block_20
  badTest_4864_block_21)
  (interval_append badTest_4864 176 184 192
  badTest_4864_block_22
  badTest_4864_block_23)))
  (interval_append badTest_4864 192 224 256
  (interval_append badTest_4864 192 208 224
  (interval_append badTest_4864 192 200 208
  badTest_4864_block_24
  badTest_4864_block_25)
  (interval_append badTest_4864 208 216 224
  badTest_4864_block_26
  badTest_4864_block_27))
  (interval_append badTest_4864 224 240 256
  (interval_append badTest_4864 224 232 240
  badTest_4864_block_28
  badTest_4864_block_29)
  (interval_append badTest_4864 240 248 256
  badTest_4864_block_30
  badTest_4864_block_31)))))
cert_badTestInterval 4864 5120
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad020 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 5120
cert_badTest_block 5120 0 0 8 8
cert_badTest_block 5120 1 8 16 8
cert_badTest_block 5120 2 16 24 8
cert_badTest_block 5120 3 24 32 8
cert_badTest_block 5120 4 32 40 8
cert_badTest_block 5120 5 40 48 8
cert_badTest_block 5120 6 48 56 8
cert_badTest_block 5120 7 56 64 8
cert_badTest_block 5120 8 64 72 8
cert_badTest_block 5120 9 72 80 8
cert_badTest_block 5120 10 80 88 8
cert_badTest_block 5120 11 88 96 8
cert_badTest_block 5120 12 96 104 8
cert_badTest_block 5120 13 104 112 8
cert_badTest_block 5120 14 112 120 8
cert_badTest_block 5120 15 120 128 8
cert_badTest_block 5120 16 128 136 8
cert_badTest_block 5120 17 136 144 8
cert_badTest_block 5120 18 144 152 8
cert_badTest_block 5120 19 152 160 8
cert_badTest_block 5120 20 160 168 8
cert_badTest_block 5120 21 168 176 8
cert_badTest_block 5120 22 176 184 8
cert_badTest_block 5120 23 184 192 8
cert_badTest_block 5120 24 192 200 8
cert_badTest_block 5120 25 200 208 8
cert_badTest_block 5120 26 208 216 8
cert_badTest_block 5120 27 216 224 8
cert_badTest_block 5120 28 224 232 8
cert_badTest_block 5120 29 232 240 8
cert_badTest_block 5120 30 240 248 8
cert_badTest_block 5120 31 248 256 8
theorem badTest_5120_complete : Interval badTest_5120 0 256 :=
  (interval_append badTest_5120 0 128 256
  (interval_append badTest_5120 0 64 128
  (interval_append badTest_5120 0 32 64
  (interval_append badTest_5120 0 16 32
  (interval_append badTest_5120 0 8 16
  badTest_5120_block_0
  badTest_5120_block_1)
  (interval_append badTest_5120 16 24 32
  badTest_5120_block_2
  badTest_5120_block_3))
  (interval_append badTest_5120 32 48 64
  (interval_append badTest_5120 32 40 48
  badTest_5120_block_4
  badTest_5120_block_5)
  (interval_append badTest_5120 48 56 64
  badTest_5120_block_6
  badTest_5120_block_7)))
  (interval_append badTest_5120 64 96 128
  (interval_append badTest_5120 64 80 96
  (interval_append badTest_5120 64 72 80
  badTest_5120_block_8
  badTest_5120_block_9)
  (interval_append badTest_5120 80 88 96
  badTest_5120_block_10
  badTest_5120_block_11))
  (interval_append badTest_5120 96 112 128
  (interval_append badTest_5120 96 104 112
  badTest_5120_block_12
  badTest_5120_block_13)
  (interval_append badTest_5120 112 120 128
  badTest_5120_block_14
  badTest_5120_block_15))))
  (interval_append badTest_5120 128 192 256
  (interval_append badTest_5120 128 160 192
  (interval_append badTest_5120 128 144 160
  (interval_append badTest_5120 128 136 144
  badTest_5120_block_16
  badTest_5120_block_17)
  (interval_append badTest_5120 144 152 160
  badTest_5120_block_18
  badTest_5120_block_19))
  (interval_append badTest_5120 160 176 192
  (interval_append badTest_5120 160 168 176
  badTest_5120_block_20
  badTest_5120_block_21)
  (interval_append badTest_5120 176 184 192
  badTest_5120_block_22
  badTest_5120_block_23)))
  (interval_append badTest_5120 192 224 256
  (interval_append badTest_5120 192 208 224
  (interval_append badTest_5120 192 200 208
  badTest_5120_block_24
  badTest_5120_block_25)
  (interval_append badTest_5120 208 216 224
  badTest_5120_block_26
  badTest_5120_block_27))
  (interval_append badTest_5120 224 240 256
  (interval_append badTest_5120 224 232 240
  badTest_5120_block_28
  badTest_5120_block_29)
  (interval_append badTest_5120 240 248 256
  badTest_5120_block_30
  badTest_5120_block_31)))))
cert_badTestInterval 5120 5376
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad021 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 5376
cert_badTest_block 5376 0 0 8 8
cert_badTest_block 5376 1 8 16 8
cert_badTest_block 5376 2 16 24 8
cert_badTest_block 5376 3 24 32 8
cert_badTest_block 5376 4 32 40 8
cert_badTest_block 5376 5 40 48 8
cert_badTest_block 5376 6 48 56 8
cert_badTest_block 5376 7 56 64 8
cert_badTest_block 5376 8 64 72 8
cert_badTest_block 5376 9 72 80 8
cert_badTest_block 5376 10 80 88 8
cert_badTest_block 5376 11 88 96 8
cert_badTest_block 5376 12 96 104 8
cert_badTest_block 5376 13 104 112 8
cert_badTest_block 5376 14 112 120 8
cert_badTest_block 5376 15 120 128 8
cert_badTest_block 5376 16 128 136 8
cert_badTest_block 5376 17 136 144 8
cert_badTest_block 5376 18 144 152 8
cert_badTest_block 5376 19 152 160 8
cert_badTest_block 5376 20 160 168 8
cert_badTest_block 5376 21 168 176 8
cert_badTest_block 5376 22 176 184 8
cert_badTest_block 5376 23 184 192 8
cert_badTest_block 5376 24 192 200 8
cert_badTest_block 5376 25 200 208 8
cert_badTest_block 5376 26 208 216 8
cert_badTest_block 5376 27 216 224 8
cert_badTest_block 5376 28 224 232 8
cert_badTest_block 5376 29 232 240 8
cert_badTest_block 5376 30 240 248 8
cert_badTest_block 5376 31 248 256 8
theorem badTest_5376_complete : Interval badTest_5376 0 256 :=
  (interval_append badTest_5376 0 128 256
  (interval_append badTest_5376 0 64 128
  (interval_append badTest_5376 0 32 64
  (interval_append badTest_5376 0 16 32
  (interval_append badTest_5376 0 8 16
  badTest_5376_block_0
  badTest_5376_block_1)
  (interval_append badTest_5376 16 24 32
  badTest_5376_block_2
  badTest_5376_block_3))
  (interval_append badTest_5376 32 48 64
  (interval_append badTest_5376 32 40 48
  badTest_5376_block_4
  badTest_5376_block_5)
  (interval_append badTest_5376 48 56 64
  badTest_5376_block_6
  badTest_5376_block_7)))
  (interval_append badTest_5376 64 96 128
  (interval_append badTest_5376 64 80 96
  (interval_append badTest_5376 64 72 80
  badTest_5376_block_8
  badTest_5376_block_9)
  (interval_append badTest_5376 80 88 96
  badTest_5376_block_10
  badTest_5376_block_11))
  (interval_append badTest_5376 96 112 128
  (interval_append badTest_5376 96 104 112
  badTest_5376_block_12
  badTest_5376_block_13)
  (interval_append badTest_5376 112 120 128
  badTest_5376_block_14
  badTest_5376_block_15))))
  (interval_append badTest_5376 128 192 256
  (interval_append badTest_5376 128 160 192
  (interval_append badTest_5376 128 144 160
  (interval_append badTest_5376 128 136 144
  badTest_5376_block_16
  badTest_5376_block_17)
  (interval_append badTest_5376 144 152 160
  badTest_5376_block_18
  badTest_5376_block_19))
  (interval_append badTest_5376 160 176 192
  (interval_append badTest_5376 160 168 176
  badTest_5376_block_20
  badTest_5376_block_21)
  (interval_append badTest_5376 176 184 192
  badTest_5376_block_22
  badTest_5376_block_23)))
  (interval_append badTest_5376 192 224 256
  (interval_append badTest_5376 192 208 224
  (interval_append badTest_5376 192 200 208
  badTest_5376_block_24
  badTest_5376_block_25)
  (interval_append badTest_5376 208 216 224
  badTest_5376_block_26
  badTest_5376_block_27))
  (interval_append badTest_5376 224 240 256
  (interval_append badTest_5376 224 232 240
  badTest_5376_block_28
  badTest_5376_block_29)
  (interval_append badTest_5376 240 248 256
  badTest_5376_block_30
  badTest_5376_block_31)))))
cert_badTestInterval 5376 5632
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
