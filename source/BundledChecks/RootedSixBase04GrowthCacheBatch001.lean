module
prelude
public meta import LowerSchemas.BundledChecks
public import RootedSixBase04GrowthCacheData

/- RootedSixBase04GrowthCacheBad004 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 1024
cert_badTest_block 1024 0 0 8 8
cert_badTest_block 1024 1 8 16 8
cert_badTest_block 1024 2 16 24 8
cert_badTest_block 1024 3 24 32 8
cert_badTest_block 1024 4 32 40 8
cert_badTest_block 1024 5 40 48 8
cert_badTest_block 1024 6 48 56 8
cert_badTest_block 1024 7 56 64 8
cert_badTest_block 1024 8 64 72 8
cert_badTest_block 1024 9 72 80 8
cert_badTest_block 1024 10 80 88 8
cert_badTest_block 1024 11 88 96 8
cert_badTest_block 1024 12 96 104 8
cert_badTest_block 1024 13 104 112 8
cert_badTest_block 1024 14 112 120 8
cert_badTest_block 1024 15 120 128 8
cert_badTest_block 1024 16 128 136 8
cert_badTest_block 1024 17 136 144 8
cert_badTest_block 1024 18 144 152 8
cert_badTest_block 1024 19 152 160 8
cert_badTest_block 1024 20 160 168 8
cert_badTest_block 1024 21 168 176 8
cert_badTest_block 1024 22 176 184 8
cert_badTest_block 1024 23 184 192 8
cert_badTest_block 1024 24 192 200 8
cert_badTest_block 1024 25 200 208 8
cert_badTest_block 1024 26 208 216 8
cert_badTest_block 1024 27 216 224 8
cert_badTest_block 1024 28 224 232 8
cert_badTest_block 1024 29 232 240 8
cert_badTest_block 1024 30 240 248 8
cert_badTest_block 1024 31 248 256 8
theorem badTest_1024_complete : Interval badTest_1024 0 256 :=
  (interval_append badTest_1024 0 128 256
  (interval_append badTest_1024 0 64 128
  (interval_append badTest_1024 0 32 64
  (interval_append badTest_1024 0 16 32
  (interval_append badTest_1024 0 8 16
  badTest_1024_block_0
  badTest_1024_block_1)
  (interval_append badTest_1024 16 24 32
  badTest_1024_block_2
  badTest_1024_block_3))
  (interval_append badTest_1024 32 48 64
  (interval_append badTest_1024 32 40 48
  badTest_1024_block_4
  badTest_1024_block_5)
  (interval_append badTest_1024 48 56 64
  badTest_1024_block_6
  badTest_1024_block_7)))
  (interval_append badTest_1024 64 96 128
  (interval_append badTest_1024 64 80 96
  (interval_append badTest_1024 64 72 80
  badTest_1024_block_8
  badTest_1024_block_9)
  (interval_append badTest_1024 80 88 96
  badTest_1024_block_10
  badTest_1024_block_11))
  (interval_append badTest_1024 96 112 128
  (interval_append badTest_1024 96 104 112
  badTest_1024_block_12
  badTest_1024_block_13)
  (interval_append badTest_1024 112 120 128
  badTest_1024_block_14
  badTest_1024_block_15))))
  (interval_append badTest_1024 128 192 256
  (interval_append badTest_1024 128 160 192
  (interval_append badTest_1024 128 144 160
  (interval_append badTest_1024 128 136 144
  badTest_1024_block_16
  badTest_1024_block_17)
  (interval_append badTest_1024 144 152 160
  badTest_1024_block_18
  badTest_1024_block_19))
  (interval_append badTest_1024 160 176 192
  (interval_append badTest_1024 160 168 176
  badTest_1024_block_20
  badTest_1024_block_21)
  (interval_append badTest_1024 176 184 192
  badTest_1024_block_22
  badTest_1024_block_23)))
  (interval_append badTest_1024 192 224 256
  (interval_append badTest_1024 192 208 224
  (interval_append badTest_1024 192 200 208
  badTest_1024_block_24
  badTest_1024_block_25)
  (interval_append badTest_1024 208 216 224
  badTest_1024_block_26
  badTest_1024_block_27))
  (interval_append badTest_1024 224 240 256
  (interval_append badTest_1024 224 232 240
  badTest_1024_block_28
  badTest_1024_block_29)
  (interval_append badTest_1024 240 248 256
  badTest_1024_block_30
  badTest_1024_block_31)))))
cert_badTestInterval 1024 1280
end Papers.RationalityTen.RootedCaches.RootedSixBase04

end
end
/- RootedSixBase04GrowthCacheBad005 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 1280
cert_badTest_block 1280 0 0 8 8
cert_badTest_block 1280 1 8 16 8
cert_badTest_block 1280 2 16 24 8
cert_badTest_block 1280 3 24 32 8
cert_badTest_block 1280 4 32 40 8
cert_badTest_block 1280 5 40 48 8
cert_badTest_block 1280 6 48 56 8
cert_badTest_block 1280 7 56 64 8
cert_badTest_block 1280 8 64 72 8
cert_badTest_block 1280 9 72 80 8
cert_badTest_block 1280 10 80 88 8
cert_badTest_block 1280 11 88 96 8
cert_badTest_block 1280 12 96 104 8
cert_badTest_block 1280 13 104 112 8
cert_badTest_block 1280 14 112 120 8
cert_badTest_block 1280 15 120 128 8
cert_badTest_block 1280 16 128 136 8
cert_badTest_block 1280 17 136 144 8
cert_badTest_block 1280 18 144 152 8
cert_badTest_block 1280 19 152 160 8
cert_badTest_block 1280 20 160 168 8
cert_badTest_block 1280 21 168 176 8
cert_badTest_block 1280 22 176 184 8
cert_badTest_block 1280 23 184 192 8
cert_badTest_block 1280 24 192 200 8
cert_badTest_block 1280 25 200 208 8
cert_badTest_block 1280 26 208 216 8
cert_badTest_block 1280 27 216 224 8
cert_badTest_block 1280 28 224 232 8
cert_badTest_block 1280 29 232 240 8
cert_badTest_block 1280 30 240 248 8
cert_badTest_block 1280 31 248 256 8
theorem badTest_1280_complete : Interval badTest_1280 0 256 :=
  (interval_append badTest_1280 0 128 256
  (interval_append badTest_1280 0 64 128
  (interval_append badTest_1280 0 32 64
  (interval_append badTest_1280 0 16 32
  (interval_append badTest_1280 0 8 16
  badTest_1280_block_0
  badTest_1280_block_1)
  (interval_append badTest_1280 16 24 32
  badTest_1280_block_2
  badTest_1280_block_3))
  (interval_append badTest_1280 32 48 64
  (interval_append badTest_1280 32 40 48
  badTest_1280_block_4
  badTest_1280_block_5)
  (interval_append badTest_1280 48 56 64
  badTest_1280_block_6
  badTest_1280_block_7)))
  (interval_append badTest_1280 64 96 128
  (interval_append badTest_1280 64 80 96
  (interval_append badTest_1280 64 72 80
  badTest_1280_block_8
  badTest_1280_block_9)
  (interval_append badTest_1280 80 88 96
  badTest_1280_block_10
  badTest_1280_block_11))
  (interval_append badTest_1280 96 112 128
  (interval_append badTest_1280 96 104 112
  badTest_1280_block_12
  badTest_1280_block_13)
  (interval_append badTest_1280 112 120 128
  badTest_1280_block_14
  badTest_1280_block_15))))
  (interval_append badTest_1280 128 192 256
  (interval_append badTest_1280 128 160 192
  (interval_append badTest_1280 128 144 160
  (interval_append badTest_1280 128 136 144
  badTest_1280_block_16
  badTest_1280_block_17)
  (interval_append badTest_1280 144 152 160
  badTest_1280_block_18
  badTest_1280_block_19))
  (interval_append badTest_1280 160 176 192
  (interval_append badTest_1280 160 168 176
  badTest_1280_block_20
  badTest_1280_block_21)
  (interval_append badTest_1280 176 184 192
  badTest_1280_block_22
  badTest_1280_block_23)))
  (interval_append badTest_1280 192 224 256
  (interval_append badTest_1280 192 208 224
  (interval_append badTest_1280 192 200 208
  badTest_1280_block_24
  badTest_1280_block_25)
  (interval_append badTest_1280 208 216 224
  badTest_1280_block_26
  badTest_1280_block_27))
  (interval_append badTest_1280 224 240 256
  (interval_append badTest_1280 224 232 240
  badTest_1280_block_28
  badTest_1280_block_29)
  (interval_append badTest_1280 240 248 256
  badTest_1280_block_30
  badTest_1280_block_31)))))
cert_badTestInterval 1280 1536
end Papers.RationalityTen.RootedCaches.RootedSixBase04

end
end
/- RootedSixBase04GrowthCacheBad006 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
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
end Papers.RationalityTen.RootedCaches.RootedSixBase04

end
end
/- RootedSixBase04GrowthCacheBad007 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
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
end Papers.RationalityTen.RootedCaches.RootedSixBase04

end
end
/- RootedSixBase04GrowthCacheBad008 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
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
end Papers.RationalityTen.RootedCaches.RootedSixBase04

end
end
/- RootedSixBase04GrowthCacheBad009 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
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
end Papers.RationalityTen.RootedCaches.RootedSixBase04

end
end
/- RootedSixBase04GrowthCacheBad010 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
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
end Papers.RationalityTen.RootedCaches.RootedSixBase04

end
end
/- RootedSixBase04GrowthCacheBad011 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 2816
cert_badTest_block 2816 0 0 8 8
theorem badTest_2816_complete : Interval badTest_2816 0 8 :=
  badTest_2816_block_0
cert_badTestInterval 2816 2824
end Papers.RationalityTen.RootedCaches.RootedSixBase04

end
end
/- RootedSixBase04GrowthCacheRidges000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_ridgeTest 0
cert_ridgeTest_block 0 0 0 8
cert_ridgeTest_block 0 1 8 16
cert_ridgeTest_block 0 2 16 24
cert_ridgeTest_block 0 3 24 32
cert_ridgeTest_block 0 4 32 40
cert_ridgeTest_block 0 5 40 48
cert_ridgeTest_block 0 6 48 56
cert_ridgeTest_block 0 7 56 64
cert_ridgeTest_block 0 8 64 72
cert_ridgeTest_block 0 9 72 80
cert_ridgeTest_block 0 10 80 88
cert_ridgeTest_block 0 11 88 96
cert_ridgeTest_block 0 12 96 104
cert_ridgeTest_block 0 13 104 112
cert_ridgeTest_block 0 14 112 120
cert_ridgeTest_block 0 15 120 128
cert_ridgeTest_complete 0
cert_ridgeTestInterval 0 128
end Papers.RationalityTen.RootedCaches.RootedSixBase04

end
end
/- RootedSixBase04GrowthCacheRidges001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_ridgeTest 128
cert_ridgeTest_block 128 0 0 8
cert_ridgeTest_block 128 1 8 16
cert_ridgeTest_block 128 2 16 24
cert_ridgeTest_block 128 3 24 32
cert_ridgeTest_block 128 4 32 40
cert_ridgeTest_block 128 5 40 48
cert_ridgeTest_block 128 6 48 56
cert_ridgeTest_block 128 7 56 64
cert_ridgeTest_block 128 8 64 72
cert_ridgeTest_block 128 9 72 80
cert_ridgeTest_block 128 10 80 88
cert_ridgeTest_block 128 11 88 96
cert_ridgeTest_block 128 12 96 104
cert_ridgeTest_block 128 13 104 112
cert_ridgeTest_block 128 14 112 120
cert_ridgeTest_block 128 15 120 128
cert_ridgeTest_complete 128
cert_ridgeTestInterval 128 256
end Papers.RationalityTen.RootedCaches.RootedSixBase04

end
end
/- RootedSixBase04GrowthCacheRidges002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_ridgeTest 256
cert_ridgeTest_block 256 0 0 8
cert_ridgeTest_block 256 1 8 16
cert_ridgeTest_block 256 2 16 24
cert_ridgeTest_block 256 3 24 32
cert_ridgeTest_block 256 4 32 40
cert_ridgeTest_block 256 5 40 48
cert_ridgeTest_block 256 6 48 56
cert_ridgeTest_block 256 7 56 64
cert_ridgeTest_block 256 8 64 72
cert_ridgeTest_block 256 9 72 80
cert_ridgeTest_block 256 10 80 88
cert_ridgeTest_block 256 11 88 96
cert_ridgeTest_block 256 12 96 104
cert_ridgeTest_block 256 13 104 112
cert_ridgeTest_block 256 14 112 120
cert_ridgeTest_block 256 15 120 128
cert_ridgeTest_complete 256
cert_ridgeTestInterval 256 384
end Papers.RationalityTen.RootedCaches.RootedSixBase04

end
end
/- RootedSixBase04GrowthCacheRidges004 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_ridgeTest 512
cert_ridgeTest_block 512 0 0 8
cert_ridgeTest_block 512 1 8 16
cert_ridgeTest_block 512 2 16 24
cert_ridgeTest_block 512 3 24 32
cert_ridgeTest_block 512 4 32 40
cert_ridgeTest_block 512 5 40 48
cert_ridgeTest_block 512 6 48 56
cert_ridgeTest_block 512 7 56 64
cert_ridgeTest_block 512 8 64 72
cert_ridgeTest_block 512 9 72 80
cert_ridgeTest_block 512 10 80 88
cert_ridgeTest_block 512 11 88 96
cert_ridgeTest_block 512 12 96 104
cert_ridgeTest_block 512 13 104 112
cert_ridgeTest_block 512 14 112 120
cert_ridgeTest_block 512 15 120 128
cert_ridgeTest_complete 512
cert_ridgeTestInterval 512 640
end Papers.RationalityTen.RootedCaches.RootedSixBase04

end
end
/- RootedSixBase04GrowthCacheWellFormed000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest 0
cert_wellFormedTest_block 0 0 0 16 16
cert_wellFormedTest_block 0 1 16 32 16
cert_wellFormedTest_block 0 2 32 48 16
cert_wellFormedTest_block 0 3 48 64 16
cert_wellFormedTest_block 0 4 64 80 16
cert_wellFormedTest_block 0 5 80 96 16
cert_wellFormedTest_block 0 6 96 112 16
cert_wellFormedTest_block 0 7 112 128 16
cert_wellFormedTest_block 0 8 128 144 16
cert_wellFormedTest_block 0 9 144 160 16
cert_wellFormedTest_block 0 10 160 176 16
cert_wellFormedTest_block 0 11 176 192 16
cert_wellFormedTest_block 0 12 192 208 16
cert_wellFormedTest_block 0 13 208 224 16
cert_wellFormedTest_block 0 14 224 240 16
cert_wellFormedTest_block 0 15 240 256 16
cert_wellFormedTest_complete 0 256
cert_wellFormedTestInterval 0 256
end Papers.RationalityTen.RootedCaches.RootedSixBase04

end
end
/- RootedSixBase04GrowthCacheWellFormed001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest 256
cert_wellFormedTest_block 256 0 0 16 16
cert_wellFormedTest_block 256 1 16 32 16
cert_wellFormedTest_block 256 2 32 48 16
cert_wellFormedTest_block 256 3 48 64 16
cert_wellFormedTest_block 256 4 64 80 16
cert_wellFormedTest_block 256 5 80 96 16
cert_wellFormedTest_block 256 6 96 112 16
cert_wellFormedTest_block 256 7 112 128 16
cert_wellFormedTest_block 256 8 128 144 16
cert_wellFormedTest_block 256 9 144 160 16
cert_wellFormedTest_block 256 10 160 176 16
cert_wellFormedTest_block 256 11 176 192 16
cert_wellFormedTest_block 256 12 192 208 16
cert_wellFormedTest_block 256 13 208 224 16
cert_wellFormedTest_block 256 14 224 240 16
cert_wellFormedTest_block 256 15 240 256 16
cert_wellFormedTest_complete 256 256
cert_wellFormedTestInterval 256 512
end Papers.RationalityTen.RootedCaches.RootedSixBase04

end
end
/- RootedSixBase04GrowthCacheWellFormed002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest 512
cert_wellFormedTest_block 512 0 0 16 16
cert_wellFormedTest_block 512 1 16 32 16
cert_wellFormedTest_block 512 2 32 48 16
cert_wellFormedTest_block 512 3 48 64 16
cert_wellFormedTest_block 512 4 64 80 16
cert_wellFormedTest_block 512 5 80 96 16
cert_wellFormedTest_block 512 6 96 112 16
cert_wellFormedTest_block 512 7 112 128 16
cert_wellFormedTest_block 512 8 128 144 16
cert_wellFormedTest_block 512 9 144 160 16
cert_wellFormedTest_block 512 10 160 176 16
cert_wellFormedTest_block 512 11 176 192 16
cert_wellFormedTest_block 512 12 192 208 16
cert_wellFormedTest_block 512 13 208 224 16
cert_wellFormedTest_block 512 14 224 240 16
cert_wellFormedTest_block 512 15 240 256 16
cert_wellFormedTest_complete 512 256
cert_wellFormedTestInterval 512 768
end Papers.RationalityTen.RootedCaches.RootedSixBase04

end
end
/- RootedSixBase04GrowthCacheWellFormed003 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest 768
cert_wellFormedTest_block 768 0 0 16 16
cert_wellFormedTest_block 768 1 16 32 16
cert_wellFormedTest_block 768 2 32 48 16
cert_wellFormedTest_block 768 3 48 64 16
cert_wellFormedTest_block 768 4 64 80 16
cert_wellFormedTest_block 768 5 80 96 16
cert_wellFormedTest_block 768 6 96 112 16
cert_wellFormedTest_block 768 7 112 128 16
cert_wellFormedTest_block 768 8 128 144 16
cert_wellFormedTest_block 768 9 144 160 16
cert_wellFormedTest_block 768 10 160 176 16
cert_wellFormedTest_block 768 11 176 192 16
cert_wellFormedTest_block 768 12 192 208 16
cert_wellFormedTest_block 768 13 208 224 16
cert_wellFormedTest_block 768 14 224 240 16
cert_wellFormedTest_block 768 15 240 256 16
cert_wellFormedTest_complete 768 256
cert_wellFormedTestInterval 768 1024
end Papers.RationalityTen.RootedCaches.RootedSixBase04

end
end
