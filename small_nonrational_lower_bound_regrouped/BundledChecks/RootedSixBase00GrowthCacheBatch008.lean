module
prelude
public meta import LowerSchemas.BundledChecks
public import RootedSixBase00GrowthCacheData

/- RootedSixBase00GrowthCacheBad042 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 10752
cert_badTest_block 10752 0 0 8 8
cert_badTest_block 10752 1 8 16 8
cert_badTest_block 10752 2 16 24 8
cert_badTest_block 10752 3 24 32 8
cert_badTest_block 10752 4 32 40 8
cert_badTest_block 10752 5 40 48 8
cert_badTest_block 10752 6 48 56 8
cert_badTest_block 10752 7 56 64 8
cert_badTest_block 10752 8 64 72 8
cert_badTest_block 10752 9 72 80 8
cert_badTest_block 10752 10 80 88 8
cert_badTest_block 10752 11 88 96 8
cert_badTest_block 10752 12 96 104 8
cert_badTest_block 10752 13 104 112 8
cert_badTest_block 10752 14 112 120 8
cert_badTest_block 10752 15 120 128 8
cert_badTest_block 10752 16 128 136 8
cert_badTest_block 10752 17 136 144 8
cert_badTest_block 10752 18 144 152 8
cert_badTest_block 10752 19 152 160 8
cert_badTest_block 10752 20 160 168 8
cert_badTest_block 10752 21 168 176 8
cert_badTest_block 10752 22 176 184 8
cert_badTest_block 10752 23 184 192 8
cert_badTest_block 10752 24 192 200 8
cert_badTest_block 10752 25 200 208 8
cert_badTest_block 10752 26 208 216 8
cert_badTest_block 10752 27 216 224 8
cert_badTest_block 10752 28 224 232 8
cert_badTest_block 10752 29 232 240 8
cert_badTest_block 10752 30 240 248 8
cert_badTest_block 10752 31 248 256 8
theorem badTest_10752_complete : Interval badTest_10752 0 256 :=
  (interval_append badTest_10752 0 128 256
  (interval_append badTest_10752 0 64 128
  (interval_append badTest_10752 0 32 64
  (interval_append badTest_10752 0 16 32
  (interval_append badTest_10752 0 8 16
  badTest_10752_block_0
  badTest_10752_block_1)
  (interval_append badTest_10752 16 24 32
  badTest_10752_block_2
  badTest_10752_block_3))
  (interval_append badTest_10752 32 48 64
  (interval_append badTest_10752 32 40 48
  badTest_10752_block_4
  badTest_10752_block_5)
  (interval_append badTest_10752 48 56 64
  badTest_10752_block_6
  badTest_10752_block_7)))
  (interval_append badTest_10752 64 96 128
  (interval_append badTest_10752 64 80 96
  (interval_append badTest_10752 64 72 80
  badTest_10752_block_8
  badTest_10752_block_9)
  (interval_append badTest_10752 80 88 96
  badTest_10752_block_10
  badTest_10752_block_11))
  (interval_append badTest_10752 96 112 128
  (interval_append badTest_10752 96 104 112
  badTest_10752_block_12
  badTest_10752_block_13)
  (interval_append badTest_10752 112 120 128
  badTest_10752_block_14
  badTest_10752_block_15))))
  (interval_append badTest_10752 128 192 256
  (interval_append badTest_10752 128 160 192
  (interval_append badTest_10752 128 144 160
  (interval_append badTest_10752 128 136 144
  badTest_10752_block_16
  badTest_10752_block_17)
  (interval_append badTest_10752 144 152 160
  badTest_10752_block_18
  badTest_10752_block_19))
  (interval_append badTest_10752 160 176 192
  (interval_append badTest_10752 160 168 176
  badTest_10752_block_20
  badTest_10752_block_21)
  (interval_append badTest_10752 176 184 192
  badTest_10752_block_22
  badTest_10752_block_23)))
  (interval_append badTest_10752 192 224 256
  (interval_append badTest_10752 192 208 224
  (interval_append badTest_10752 192 200 208
  badTest_10752_block_24
  badTest_10752_block_25)
  (interval_append badTest_10752 208 216 224
  badTest_10752_block_26
  badTest_10752_block_27))
  (interval_append badTest_10752 224 240 256
  (interval_append badTest_10752 224 232 240
  badTest_10752_block_28
  badTest_10752_block_29)
  (interval_append badTest_10752 240 248 256
  badTest_10752_block_30
  badTest_10752_block_31)))))
cert_badTestInterval 10752 11008
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad043 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 11008
cert_badTest_block 11008 0 0 8 8
cert_badTest_block 11008 1 8 16 8
cert_badTest_block 11008 2 16 24 8
cert_badTest_block 11008 3 24 32 8
cert_badTest_block 11008 4 32 40 8
cert_badTest_block 11008 5 40 48 8
cert_badTest_block 11008 6 48 56 8
cert_badTest_block 11008 7 56 64 8
cert_badTest_block 11008 8 64 72 8
cert_badTest_block 11008 9 72 80 8
cert_badTest_block 11008 10 80 88 8
cert_badTest_block 11008 11 88 96 8
cert_badTest_block 11008 12 96 104 8
cert_badTest_block 11008 13 104 112 8
cert_badTest_block 11008 14 112 120 8
cert_badTest_block 11008 15 120 128 8
cert_badTest_block 11008 16 128 136 8
cert_badTest_block 11008 17 136 144 8
cert_badTest_block 11008 18 144 152 8
cert_badTest_block 11008 19 152 160 8
cert_badTest_block 11008 20 160 168 8
cert_badTest_block 11008 21 168 176 8
cert_badTest_block 11008 22 176 184 8
cert_badTest_block 11008 23 184 192 8
cert_badTest_block 11008 24 192 200 8
cert_badTest_block 11008 25 200 208 8
cert_badTest_block 11008 26 208 216 8
cert_badTest_block 11008 27 216 224 8
cert_badTest_block 11008 28 224 232 8
cert_badTest_block 11008 29 232 240 8
cert_badTest_block 11008 30 240 248 8
cert_badTest_block 11008 31 248 256 8
theorem badTest_11008_complete : Interval badTest_11008 0 256 :=
  (interval_append badTest_11008 0 128 256
  (interval_append badTest_11008 0 64 128
  (interval_append badTest_11008 0 32 64
  (interval_append badTest_11008 0 16 32
  (interval_append badTest_11008 0 8 16
  badTest_11008_block_0
  badTest_11008_block_1)
  (interval_append badTest_11008 16 24 32
  badTest_11008_block_2
  badTest_11008_block_3))
  (interval_append badTest_11008 32 48 64
  (interval_append badTest_11008 32 40 48
  badTest_11008_block_4
  badTest_11008_block_5)
  (interval_append badTest_11008 48 56 64
  badTest_11008_block_6
  badTest_11008_block_7)))
  (interval_append badTest_11008 64 96 128
  (interval_append badTest_11008 64 80 96
  (interval_append badTest_11008 64 72 80
  badTest_11008_block_8
  badTest_11008_block_9)
  (interval_append badTest_11008 80 88 96
  badTest_11008_block_10
  badTest_11008_block_11))
  (interval_append badTest_11008 96 112 128
  (interval_append badTest_11008 96 104 112
  badTest_11008_block_12
  badTest_11008_block_13)
  (interval_append badTest_11008 112 120 128
  badTest_11008_block_14
  badTest_11008_block_15))))
  (interval_append badTest_11008 128 192 256
  (interval_append badTest_11008 128 160 192
  (interval_append badTest_11008 128 144 160
  (interval_append badTest_11008 128 136 144
  badTest_11008_block_16
  badTest_11008_block_17)
  (interval_append badTest_11008 144 152 160
  badTest_11008_block_18
  badTest_11008_block_19))
  (interval_append badTest_11008 160 176 192
  (interval_append badTest_11008 160 168 176
  badTest_11008_block_20
  badTest_11008_block_21)
  (interval_append badTest_11008 176 184 192
  badTest_11008_block_22
  badTest_11008_block_23)))
  (interval_append badTest_11008 192 224 256
  (interval_append badTest_11008 192 208 224
  (interval_append badTest_11008 192 200 208
  badTest_11008_block_24
  badTest_11008_block_25)
  (interval_append badTest_11008 208 216 224
  badTest_11008_block_26
  badTest_11008_block_27))
  (interval_append badTest_11008 224 240 256
  (interval_append badTest_11008 224 232 240
  badTest_11008_block_28
  badTest_11008_block_29)
  (interval_append badTest_11008 240 248 256
  badTest_11008_block_30
  badTest_11008_block_31)))))
cert_badTestInterval 11008 11264
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad044 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 11264
cert_badTest_block 11264 0 0 8 8
cert_badTest_block 11264 1 8 16 8
cert_badTest_block 11264 2 16 24 8
cert_badTest_block 11264 3 24 32 8
cert_badTest_block 11264 4 32 40 8
cert_badTest_block 11264 5 40 48 8
cert_badTest_block 11264 6 48 56 8
cert_badTest_block 11264 7 56 64 8
cert_badTest_block 11264 8 64 72 8
cert_badTest_block 11264 9 72 80 8
cert_badTest_block 11264 10 80 88 8
cert_badTest_block 11264 11 88 96 8
cert_badTest_block 11264 12 96 104 8
cert_badTest_block 11264 13 104 112 8
cert_badTest_block 11264 14 112 120 8
cert_badTest_block 11264 15 120 128 8
cert_badTest_block 11264 16 128 136 8
cert_badTest_block 11264 17 136 144 8
cert_badTest_block 11264 18 144 152 8
cert_badTest_block 11264 19 152 160 8
cert_badTest_block 11264 20 160 168 8
cert_badTest_block 11264 21 168 176 8
cert_badTest_block 11264 22 176 184 8
cert_badTest_block 11264 23 184 192 8
cert_badTest_block 11264 24 192 200 8
cert_badTest_block 11264 25 200 208 8
cert_badTest_block 11264 26 208 216 8
cert_badTest_block 11264 27 216 224 8
cert_badTest_block 11264 28 224 232 8
cert_badTest_block 11264 29 232 240 8
cert_badTest_block 11264 30 240 248 8
cert_badTest_block 11264 31 248 256 8
theorem badTest_11264_complete : Interval badTest_11264 0 256 :=
  (interval_append badTest_11264 0 128 256
  (interval_append badTest_11264 0 64 128
  (interval_append badTest_11264 0 32 64
  (interval_append badTest_11264 0 16 32
  (interval_append badTest_11264 0 8 16
  badTest_11264_block_0
  badTest_11264_block_1)
  (interval_append badTest_11264 16 24 32
  badTest_11264_block_2
  badTest_11264_block_3))
  (interval_append badTest_11264 32 48 64
  (interval_append badTest_11264 32 40 48
  badTest_11264_block_4
  badTest_11264_block_5)
  (interval_append badTest_11264 48 56 64
  badTest_11264_block_6
  badTest_11264_block_7)))
  (interval_append badTest_11264 64 96 128
  (interval_append badTest_11264 64 80 96
  (interval_append badTest_11264 64 72 80
  badTest_11264_block_8
  badTest_11264_block_9)
  (interval_append badTest_11264 80 88 96
  badTest_11264_block_10
  badTest_11264_block_11))
  (interval_append badTest_11264 96 112 128
  (interval_append badTest_11264 96 104 112
  badTest_11264_block_12
  badTest_11264_block_13)
  (interval_append badTest_11264 112 120 128
  badTest_11264_block_14
  badTest_11264_block_15))))
  (interval_append badTest_11264 128 192 256
  (interval_append badTest_11264 128 160 192
  (interval_append badTest_11264 128 144 160
  (interval_append badTest_11264 128 136 144
  badTest_11264_block_16
  badTest_11264_block_17)
  (interval_append badTest_11264 144 152 160
  badTest_11264_block_18
  badTest_11264_block_19))
  (interval_append badTest_11264 160 176 192
  (interval_append badTest_11264 160 168 176
  badTest_11264_block_20
  badTest_11264_block_21)
  (interval_append badTest_11264 176 184 192
  badTest_11264_block_22
  badTest_11264_block_23)))
  (interval_append badTest_11264 192 224 256
  (interval_append badTest_11264 192 208 224
  (interval_append badTest_11264 192 200 208
  badTest_11264_block_24
  badTest_11264_block_25)
  (interval_append badTest_11264 208 216 224
  badTest_11264_block_26
  badTest_11264_block_27))
  (interval_append badTest_11264 224 240 256
  (interval_append badTest_11264 224 232 240
  badTest_11264_block_28
  badTest_11264_block_29)
  (interval_append badTest_11264 240 248 256
  badTest_11264_block_30
  badTest_11264_block_31)))))
cert_badTestInterval 11264 11520
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad045 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 11520
cert_badTest_block 11520 0 0 8 8
cert_badTest_block 11520 1 8 16 8
cert_badTest_block 11520 2 16 24 8
cert_badTest_block 11520 3 24 32 8
cert_badTest_block 11520 4 32 40 8
cert_badTest_block 11520 5 40 48 8
cert_badTest_block 11520 6 48 56 8
cert_badTest_block 11520 7 56 64 8
cert_badTest_block 11520 8 64 72 8
cert_badTest_block 11520 9 72 80 8
cert_badTest_block 11520 10 80 88 8
cert_badTest_block 11520 11 88 96 8
cert_badTest_block 11520 12 96 104 8
cert_badTest_block 11520 13 104 112 8
cert_badTest_block 11520 14 112 120 8
cert_badTest_block 11520 15 120 128 8
cert_badTest_block 11520 16 128 136 8
cert_badTest_block 11520 17 136 144 8
cert_badTest_block 11520 18 144 152 8
cert_badTest_block 11520 19 152 160 8
cert_badTest_block 11520 20 160 168 8
cert_badTest_block 11520 21 168 176 8
cert_badTest_block 11520 22 176 184 8
cert_badTest_block 11520 23 184 192 8
cert_badTest_block 11520 24 192 200 8
cert_badTest_block 11520 25 200 208 8
cert_badTest_block 11520 26 208 216 8
cert_badTest_block 11520 27 216 224 8
cert_badTest_block 11520 28 224 232 8
cert_badTest_block 11520 29 232 240 8
cert_badTest_block 11520 30 240 248 8
cert_badTest_block 11520 31 248 256 8
theorem badTest_11520_complete : Interval badTest_11520 0 256 :=
  (interval_append badTest_11520 0 128 256
  (interval_append badTest_11520 0 64 128
  (interval_append badTest_11520 0 32 64
  (interval_append badTest_11520 0 16 32
  (interval_append badTest_11520 0 8 16
  badTest_11520_block_0
  badTest_11520_block_1)
  (interval_append badTest_11520 16 24 32
  badTest_11520_block_2
  badTest_11520_block_3))
  (interval_append badTest_11520 32 48 64
  (interval_append badTest_11520 32 40 48
  badTest_11520_block_4
  badTest_11520_block_5)
  (interval_append badTest_11520 48 56 64
  badTest_11520_block_6
  badTest_11520_block_7)))
  (interval_append badTest_11520 64 96 128
  (interval_append badTest_11520 64 80 96
  (interval_append badTest_11520 64 72 80
  badTest_11520_block_8
  badTest_11520_block_9)
  (interval_append badTest_11520 80 88 96
  badTest_11520_block_10
  badTest_11520_block_11))
  (interval_append badTest_11520 96 112 128
  (interval_append badTest_11520 96 104 112
  badTest_11520_block_12
  badTest_11520_block_13)
  (interval_append badTest_11520 112 120 128
  badTest_11520_block_14
  badTest_11520_block_15))))
  (interval_append badTest_11520 128 192 256
  (interval_append badTest_11520 128 160 192
  (interval_append badTest_11520 128 144 160
  (interval_append badTest_11520 128 136 144
  badTest_11520_block_16
  badTest_11520_block_17)
  (interval_append badTest_11520 144 152 160
  badTest_11520_block_18
  badTest_11520_block_19))
  (interval_append badTest_11520 160 176 192
  (interval_append badTest_11520 160 168 176
  badTest_11520_block_20
  badTest_11520_block_21)
  (interval_append badTest_11520 176 184 192
  badTest_11520_block_22
  badTest_11520_block_23)))
  (interval_append badTest_11520 192 224 256
  (interval_append badTest_11520 192 208 224
  (interval_append badTest_11520 192 200 208
  badTest_11520_block_24
  badTest_11520_block_25)
  (interval_append badTest_11520 208 216 224
  badTest_11520_block_26
  badTest_11520_block_27))
  (interval_append badTest_11520 224 240 256
  (interval_append badTest_11520 224 232 240
  badTest_11520_block_28
  badTest_11520_block_29)
  (interval_append badTest_11520 240 248 256
  badTest_11520_block_30
  badTest_11520_block_31)))))
cert_badTestInterval 11520 11776
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad046 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 11776
cert_badTest_block 11776 0 0 8 8
cert_badTest_block 11776 1 8 16 8
cert_badTest_block 11776 2 16 24 8
cert_badTest_block 11776 3 24 32 8
cert_badTest_block 11776 4 32 40 8
cert_badTest_block 11776 5 40 48 8
cert_badTest_block 11776 6 48 56 8
cert_badTest_block 11776 7 56 64 8
cert_badTest_block 11776 8 64 72 8
cert_badTest_block 11776 9 72 80 8
cert_badTest_block 11776 10 80 88 8
cert_badTest_block 11776 11 88 96 8
cert_badTest_block 11776 12 96 104 8
cert_badTest_block 11776 13 104 112 8
cert_badTest_block 11776 14 112 120 8
cert_badTest_block 11776 15 120 128 8
cert_badTest_block 11776 16 128 136 8
cert_badTest_block 11776 17 136 144 8
cert_badTest_block 11776 18 144 152 8
cert_badTest_block 11776 19 152 160 8
cert_badTest_block 11776 20 160 168 8
cert_badTest_block 11776 21 168 176 8
cert_badTest_block 11776 22 176 184 8
cert_badTest_block 11776 23 184 192 8
cert_badTest_block 11776 24 192 200 8
cert_badTest_block 11776 25 200 208 8
cert_badTest_block 11776 26 208 216 8
cert_badTest_block 11776 27 216 224 8
cert_badTest_block 11776 28 224 232 8
cert_badTest_block 11776 29 232 240 8
cert_badTest_block 11776 30 240 248 8
cert_badTest_block 11776 31 248 256 8
theorem badTest_11776_complete : Interval badTest_11776 0 256 :=
  (interval_append badTest_11776 0 128 256
  (interval_append badTest_11776 0 64 128
  (interval_append badTest_11776 0 32 64
  (interval_append badTest_11776 0 16 32
  (interval_append badTest_11776 0 8 16
  badTest_11776_block_0
  badTest_11776_block_1)
  (interval_append badTest_11776 16 24 32
  badTest_11776_block_2
  badTest_11776_block_3))
  (interval_append badTest_11776 32 48 64
  (interval_append badTest_11776 32 40 48
  badTest_11776_block_4
  badTest_11776_block_5)
  (interval_append badTest_11776 48 56 64
  badTest_11776_block_6
  badTest_11776_block_7)))
  (interval_append badTest_11776 64 96 128
  (interval_append badTest_11776 64 80 96
  (interval_append badTest_11776 64 72 80
  badTest_11776_block_8
  badTest_11776_block_9)
  (interval_append badTest_11776 80 88 96
  badTest_11776_block_10
  badTest_11776_block_11))
  (interval_append badTest_11776 96 112 128
  (interval_append badTest_11776 96 104 112
  badTest_11776_block_12
  badTest_11776_block_13)
  (interval_append badTest_11776 112 120 128
  badTest_11776_block_14
  badTest_11776_block_15))))
  (interval_append badTest_11776 128 192 256
  (interval_append badTest_11776 128 160 192
  (interval_append badTest_11776 128 144 160
  (interval_append badTest_11776 128 136 144
  badTest_11776_block_16
  badTest_11776_block_17)
  (interval_append badTest_11776 144 152 160
  badTest_11776_block_18
  badTest_11776_block_19))
  (interval_append badTest_11776 160 176 192
  (interval_append badTest_11776 160 168 176
  badTest_11776_block_20
  badTest_11776_block_21)
  (interval_append badTest_11776 176 184 192
  badTest_11776_block_22
  badTest_11776_block_23)))
  (interval_append badTest_11776 192 224 256
  (interval_append badTest_11776 192 208 224
  (interval_append badTest_11776 192 200 208
  badTest_11776_block_24
  badTest_11776_block_25)
  (interval_append badTest_11776 208 216 224
  badTest_11776_block_26
  badTest_11776_block_27))
  (interval_append badTest_11776 224 240 256
  (interval_append badTest_11776 224 232 240
  badTest_11776_block_28
  badTest_11776_block_29)
  (interval_append badTest_11776 240 248 256
  badTest_11776_block_30
  badTest_11776_block_31)))))
cert_badTestInterval 11776 12032
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad047 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 12032
cert_badTest_block 12032 0 0 8 8
cert_badTest_block 12032 1 8 16 8
cert_badTest_block 12032 2 16 24 8
cert_badTest_block 12032 3 24 32 8
cert_badTest_block 12032 4 32 40 8
cert_badTest_block 12032 5 40 48 8
cert_badTest_block 12032 6 48 56 8
cert_badTest_block 12032 7 56 64 8
cert_badTest_block 12032 8 64 72 8
cert_badTest_block 12032 9 72 80 8
cert_badTest_block 12032 10 80 88 8
cert_badTest_block 12032 11 88 96 8
cert_badTest_block 12032 12 96 104 8
cert_badTest_block 12032 13 104 112 8
cert_badTest_block 12032 14 112 120 8
cert_badTest_block 12032 15 120 128 8
cert_badTest_block 12032 16 128 136 8
cert_badTest_block 12032 17 136 144 8
cert_badTest_block 12032 18 144 152 8
cert_badTest_block 12032 19 152 160 8
cert_badTest_block 12032 20 160 168 8
cert_badTest_block 12032 21 168 176 8
cert_badTest_block 12032 22 176 184 8
cert_badTest_block 12032 23 184 192 8
cert_badTest_block 12032 24 192 200 8
cert_badTest_block 12032 25 200 208 8
cert_badTest_block 12032 26 208 216 8
cert_badTest_block 12032 27 216 224 8
cert_badTest_block 12032 28 224 232 8
cert_badTest_block 12032 29 232 240 8
cert_badTest_block 12032 30 240 248 8
cert_badTest_block 12032 31 248 256 8
theorem badTest_12032_complete : Interval badTest_12032 0 256 :=
  (interval_append badTest_12032 0 128 256
  (interval_append badTest_12032 0 64 128
  (interval_append badTest_12032 0 32 64
  (interval_append badTest_12032 0 16 32
  (interval_append badTest_12032 0 8 16
  badTest_12032_block_0
  badTest_12032_block_1)
  (interval_append badTest_12032 16 24 32
  badTest_12032_block_2
  badTest_12032_block_3))
  (interval_append badTest_12032 32 48 64
  (interval_append badTest_12032 32 40 48
  badTest_12032_block_4
  badTest_12032_block_5)
  (interval_append badTest_12032 48 56 64
  badTest_12032_block_6
  badTest_12032_block_7)))
  (interval_append badTest_12032 64 96 128
  (interval_append badTest_12032 64 80 96
  (interval_append badTest_12032 64 72 80
  badTest_12032_block_8
  badTest_12032_block_9)
  (interval_append badTest_12032 80 88 96
  badTest_12032_block_10
  badTest_12032_block_11))
  (interval_append badTest_12032 96 112 128
  (interval_append badTest_12032 96 104 112
  badTest_12032_block_12
  badTest_12032_block_13)
  (interval_append badTest_12032 112 120 128
  badTest_12032_block_14
  badTest_12032_block_15))))
  (interval_append badTest_12032 128 192 256
  (interval_append badTest_12032 128 160 192
  (interval_append badTest_12032 128 144 160
  (interval_append badTest_12032 128 136 144
  badTest_12032_block_16
  badTest_12032_block_17)
  (interval_append badTest_12032 144 152 160
  badTest_12032_block_18
  badTest_12032_block_19))
  (interval_append badTest_12032 160 176 192
  (interval_append badTest_12032 160 168 176
  badTest_12032_block_20
  badTest_12032_block_21)
  (interval_append badTest_12032 176 184 192
  badTest_12032_block_22
  badTest_12032_block_23)))
  (interval_append badTest_12032 192 224 256
  (interval_append badTest_12032 192 208 224
  (interval_append badTest_12032 192 200 208
  badTest_12032_block_24
  badTest_12032_block_25)
  (interval_append badTest_12032 208 216 224
  badTest_12032_block_26
  badTest_12032_block_27))
  (interval_append badTest_12032 224 240 256
  (interval_append badTest_12032 224 232 240
  badTest_12032_block_28
  badTest_12032_block_29)
  (interval_append badTest_12032 240 248 256
  badTest_12032_block_30
  badTest_12032_block_31)))))
cert_badTestInterval 12032 12288
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad048 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 12288
cert_badTest_block 12288 0 0 8 8
cert_badTest_block 12288 1 8 16 8
cert_badTest_block 12288 2 16 24 8
cert_badTest_block 12288 3 24 32 8
cert_badTest_block 12288 4 32 40 8
cert_badTest_block 12288 5 40 48 8
cert_badTest_block 12288 6 48 56 8
cert_badTest_block 12288 7 56 64 8
cert_badTest_block 12288 8 64 72 8
cert_badTest_block 12288 9 72 80 8
cert_badTest_block 12288 10 80 88 8
cert_badTest_block 12288 11 88 96 8
cert_badTest_block 12288 12 96 104 8
cert_badTest_block 12288 13 104 112 8
cert_badTest_block 12288 14 112 120 8
cert_badTest_block 12288 15 120 128 8
cert_badTest_block 12288 16 128 136 8
cert_badTest_block 12288 17 136 144 8
cert_badTest_block 12288 18 144 152 8
cert_badTest_block 12288 19 152 160 8
cert_badTest_block 12288 20 160 168 8
cert_badTest_block 12288 21 168 176 8
cert_badTest_block 12288 22 176 184 8
cert_badTest_block 12288 23 184 192 8
cert_badTest_block 12288 24 192 200 8
cert_badTest_block 12288 25 200 208 8
cert_badTest_block 12288 26 208 216 8
cert_badTest_block 12288 27 216 224 8
cert_badTest_block 12288 28 224 232 8
cert_badTest_block 12288 29 232 240 8
cert_badTest_block 12288 30 240 248 8
cert_badTest_block 12288 31 248 256 8
theorem badTest_12288_complete : Interval badTest_12288 0 256 :=
  (interval_append badTest_12288 0 128 256
  (interval_append badTest_12288 0 64 128
  (interval_append badTest_12288 0 32 64
  (interval_append badTest_12288 0 16 32
  (interval_append badTest_12288 0 8 16
  badTest_12288_block_0
  badTest_12288_block_1)
  (interval_append badTest_12288 16 24 32
  badTest_12288_block_2
  badTest_12288_block_3))
  (interval_append badTest_12288 32 48 64
  (interval_append badTest_12288 32 40 48
  badTest_12288_block_4
  badTest_12288_block_5)
  (interval_append badTest_12288 48 56 64
  badTest_12288_block_6
  badTest_12288_block_7)))
  (interval_append badTest_12288 64 96 128
  (interval_append badTest_12288 64 80 96
  (interval_append badTest_12288 64 72 80
  badTest_12288_block_8
  badTest_12288_block_9)
  (interval_append badTest_12288 80 88 96
  badTest_12288_block_10
  badTest_12288_block_11))
  (interval_append badTest_12288 96 112 128
  (interval_append badTest_12288 96 104 112
  badTest_12288_block_12
  badTest_12288_block_13)
  (interval_append badTest_12288 112 120 128
  badTest_12288_block_14
  badTest_12288_block_15))))
  (interval_append badTest_12288 128 192 256
  (interval_append badTest_12288 128 160 192
  (interval_append badTest_12288 128 144 160
  (interval_append badTest_12288 128 136 144
  badTest_12288_block_16
  badTest_12288_block_17)
  (interval_append badTest_12288 144 152 160
  badTest_12288_block_18
  badTest_12288_block_19))
  (interval_append badTest_12288 160 176 192
  (interval_append badTest_12288 160 168 176
  badTest_12288_block_20
  badTest_12288_block_21)
  (interval_append badTest_12288 176 184 192
  badTest_12288_block_22
  badTest_12288_block_23)))
  (interval_append badTest_12288 192 224 256
  (interval_append badTest_12288 192 208 224
  (interval_append badTest_12288 192 200 208
  badTest_12288_block_24
  badTest_12288_block_25)
  (interval_append badTest_12288 208 216 224
  badTest_12288_block_26
  badTest_12288_block_27))
  (interval_append badTest_12288 224 240 256
  (interval_append badTest_12288 224 232 240
  badTest_12288_block_28
  badTest_12288_block_29)
  (interval_append badTest_12288 240 248 256
  badTest_12288_block_30
  badTest_12288_block_31)))))
cert_badTestInterval 12288 12544
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad049 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 12544
cert_badTest_block 12544 0 0 8 8
cert_badTest_block 12544 1 8 16 8
cert_badTest_block 12544 2 16 24 8
cert_badTest_block 12544 3 24 32 8
cert_badTest_block 12544 4 32 40 8
cert_badTest_block 12544 5 40 48 8
cert_badTest_block 12544 6 48 56 8
cert_badTest_block 12544 7 56 64 8
cert_badTest_block 12544 8 64 72 8
cert_badTest_block 12544 9 72 80 8
cert_badTest_block 12544 10 80 88 8
cert_badTest_block 12544 11 88 96 8
cert_badTest_block 12544 12 96 104 8
cert_badTest_block 12544 13 104 112 8
cert_badTest_block 12544 14 112 120 8
cert_badTest_block 12544 15 120 128 8
cert_badTest_block 12544 16 128 136 8
cert_badTest_block 12544 17 136 144 8
cert_badTest_block 12544 18 144 152 8
cert_badTest_block 12544 19 152 160 8
cert_badTest_block 12544 20 160 168 8
cert_badTest_block 12544 21 168 176 8
cert_badTest_block 12544 22 176 184 8
cert_badTest_block 12544 23 184 192 8
cert_badTest_block 12544 24 192 200 8
cert_badTest_block 12544 25 200 208 8
cert_badTest_block 12544 26 208 216 8
cert_badTest_block 12544 27 216 224 8
cert_badTest_block 12544 28 224 232 8
cert_badTest_block 12544 29 232 240 8
cert_badTest_block 12544 30 240 248 8
cert_badTest_block 12544 31 248 256 8
theorem badTest_12544_complete : Interval badTest_12544 0 256 :=
  (interval_append badTest_12544 0 128 256
  (interval_append badTest_12544 0 64 128
  (interval_append badTest_12544 0 32 64
  (interval_append badTest_12544 0 16 32
  (interval_append badTest_12544 0 8 16
  badTest_12544_block_0
  badTest_12544_block_1)
  (interval_append badTest_12544 16 24 32
  badTest_12544_block_2
  badTest_12544_block_3))
  (interval_append badTest_12544 32 48 64
  (interval_append badTest_12544 32 40 48
  badTest_12544_block_4
  badTest_12544_block_5)
  (interval_append badTest_12544 48 56 64
  badTest_12544_block_6
  badTest_12544_block_7)))
  (interval_append badTest_12544 64 96 128
  (interval_append badTest_12544 64 80 96
  (interval_append badTest_12544 64 72 80
  badTest_12544_block_8
  badTest_12544_block_9)
  (interval_append badTest_12544 80 88 96
  badTest_12544_block_10
  badTest_12544_block_11))
  (interval_append badTest_12544 96 112 128
  (interval_append badTest_12544 96 104 112
  badTest_12544_block_12
  badTest_12544_block_13)
  (interval_append badTest_12544 112 120 128
  badTest_12544_block_14
  badTest_12544_block_15))))
  (interval_append badTest_12544 128 192 256
  (interval_append badTest_12544 128 160 192
  (interval_append badTest_12544 128 144 160
  (interval_append badTest_12544 128 136 144
  badTest_12544_block_16
  badTest_12544_block_17)
  (interval_append badTest_12544 144 152 160
  badTest_12544_block_18
  badTest_12544_block_19))
  (interval_append badTest_12544 160 176 192
  (interval_append badTest_12544 160 168 176
  badTest_12544_block_20
  badTest_12544_block_21)
  (interval_append badTest_12544 176 184 192
  badTest_12544_block_22
  badTest_12544_block_23)))
  (interval_append badTest_12544 192 224 256
  (interval_append badTest_12544 192 208 224
  (interval_append badTest_12544 192 200 208
  badTest_12544_block_24
  badTest_12544_block_25)
  (interval_append badTest_12544 208 216 224
  badTest_12544_block_26
  badTest_12544_block_27))
  (interval_append badTest_12544 224 240 256
  (interval_append badTest_12544 224 232 240
  badTest_12544_block_28
  badTest_12544_block_29)
  (interval_append badTest_12544 240 248 256
  badTest_12544_block_30
  badTest_12544_block_31)))))
cert_badTestInterval 12544 12800
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad050 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 12800
cert_badTest_block 12800 0 0 8 8
cert_badTest_block 12800 1 8 16 8
cert_badTest_block 12800 2 16 24 8
cert_badTest_block 12800 3 24 32 8
cert_badTest_block 12800 4 32 40 8
cert_badTest_block 12800 5 40 48 8
cert_badTest_block 12800 6 48 56 8
cert_badTest_block 12800 7 56 64 8
cert_badTest_block 12800 8 64 72 8
cert_badTest_block 12800 9 72 80 8
cert_badTest_block 12800 10 80 88 8
cert_badTest_block 12800 11 88 96 8
cert_badTest_block 12800 12 96 104 8
cert_badTest_block 12800 13 104 112 8
cert_badTest_block 12800 14 112 120 8
cert_badTest_block 12800 15 120 128 8
cert_badTest_block 12800 16 128 136 8
cert_badTest_block 12800 17 136 144 8
cert_badTest_block 12800 18 144 152 8
cert_badTest_block 12800 19 152 160 8
cert_badTest_block 12800 20 160 168 8
cert_badTest_block 12800 21 168 176 8
cert_badTest_block 12800 22 176 184 8
cert_badTest_block 12800 23 184 192 8
cert_badTest_block 12800 24 192 200 8
cert_badTest_block 12800 25 200 208 8
cert_badTest_block 12800 26 208 216 8
cert_badTest_block 12800 27 216 224 8
cert_badTest_block 12800 28 224 232 8
cert_badTest_block 12800 29 232 240 8
cert_badTest_block 12800 30 240 248 8
cert_badTest_block 12800 31 248 256 8
theorem badTest_12800_complete : Interval badTest_12800 0 256 :=
  (interval_append badTest_12800 0 128 256
  (interval_append badTest_12800 0 64 128
  (interval_append badTest_12800 0 32 64
  (interval_append badTest_12800 0 16 32
  (interval_append badTest_12800 0 8 16
  badTest_12800_block_0
  badTest_12800_block_1)
  (interval_append badTest_12800 16 24 32
  badTest_12800_block_2
  badTest_12800_block_3))
  (interval_append badTest_12800 32 48 64
  (interval_append badTest_12800 32 40 48
  badTest_12800_block_4
  badTest_12800_block_5)
  (interval_append badTest_12800 48 56 64
  badTest_12800_block_6
  badTest_12800_block_7)))
  (interval_append badTest_12800 64 96 128
  (interval_append badTest_12800 64 80 96
  (interval_append badTest_12800 64 72 80
  badTest_12800_block_8
  badTest_12800_block_9)
  (interval_append badTest_12800 80 88 96
  badTest_12800_block_10
  badTest_12800_block_11))
  (interval_append badTest_12800 96 112 128
  (interval_append badTest_12800 96 104 112
  badTest_12800_block_12
  badTest_12800_block_13)
  (interval_append badTest_12800 112 120 128
  badTest_12800_block_14
  badTest_12800_block_15))))
  (interval_append badTest_12800 128 192 256
  (interval_append badTest_12800 128 160 192
  (interval_append badTest_12800 128 144 160
  (interval_append badTest_12800 128 136 144
  badTest_12800_block_16
  badTest_12800_block_17)
  (interval_append badTest_12800 144 152 160
  badTest_12800_block_18
  badTest_12800_block_19))
  (interval_append badTest_12800 160 176 192
  (interval_append badTest_12800 160 168 176
  badTest_12800_block_20
  badTest_12800_block_21)
  (interval_append badTest_12800 176 184 192
  badTest_12800_block_22
  badTest_12800_block_23)))
  (interval_append badTest_12800 192 224 256
  (interval_append badTest_12800 192 208 224
  (interval_append badTest_12800 192 200 208
  badTest_12800_block_24
  badTest_12800_block_25)
  (interval_append badTest_12800 208 216 224
  badTest_12800_block_26
  badTest_12800_block_27))
  (interval_append badTest_12800 224 240 256
  (interval_append badTest_12800 224 232 240
  badTest_12800_block_28
  badTest_12800_block_29)
  (interval_append badTest_12800 240 248 256
  badTest_12800_block_30
  badTest_12800_block_31)))))
cert_badTestInterval 12800 13056
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad051 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 13056
cert_badTest_block 13056 0 0 8 8
cert_badTest_block 13056 1 8 16 8
cert_badTest_block 13056 2 16 24 8
cert_badTest_block 13056 3 24 32 8
cert_badTest_block 13056 4 32 40 8
cert_badTest_block 13056 5 40 48 8
cert_badTest_block 13056 6 48 56 8
cert_badTest_block 13056 7 56 64 8
cert_badTest_block 13056 8 64 72 8
cert_badTest_block 13056 9 72 80 8
cert_badTest_block 13056 10 80 88 8
cert_badTest_block 13056 11 88 96 8
cert_badTest_block 13056 12 96 104 8
cert_badTest_block 13056 13 104 112 8
cert_badTest_block 13056 14 112 120 8
cert_badTest_block 13056 15 120 128 8
cert_badTest_block 13056 16 128 136 8
cert_badTest_block 13056 17 136 144 8
cert_badTest_block 13056 18 144 152 8
cert_badTest_block 13056 19 152 160 8
cert_badTest_block 13056 20 160 168 8
cert_badTest_block 13056 21 168 176 8
cert_badTest_block 13056 22 176 184 8
cert_badTest_block 13056 23 184 192 8
cert_badTest_block 13056 24 192 200 8
cert_badTest_block 13056 25 200 208 8
cert_badTest_block 13056 26 208 216 8
cert_badTest_block 13056 27 216 224 8
cert_badTest_block 13056 28 224 232 8
cert_badTest_block 13056 29 232 240 8
cert_badTest_block 13056 30 240 248 8
cert_badTest_block 13056 31 248 256 8
theorem badTest_13056_complete : Interval badTest_13056 0 256 :=
  (interval_append badTest_13056 0 128 256
  (interval_append badTest_13056 0 64 128
  (interval_append badTest_13056 0 32 64
  (interval_append badTest_13056 0 16 32
  (interval_append badTest_13056 0 8 16
  badTest_13056_block_0
  badTest_13056_block_1)
  (interval_append badTest_13056 16 24 32
  badTest_13056_block_2
  badTest_13056_block_3))
  (interval_append badTest_13056 32 48 64
  (interval_append badTest_13056 32 40 48
  badTest_13056_block_4
  badTest_13056_block_5)
  (interval_append badTest_13056 48 56 64
  badTest_13056_block_6
  badTest_13056_block_7)))
  (interval_append badTest_13056 64 96 128
  (interval_append badTest_13056 64 80 96
  (interval_append badTest_13056 64 72 80
  badTest_13056_block_8
  badTest_13056_block_9)
  (interval_append badTest_13056 80 88 96
  badTest_13056_block_10
  badTest_13056_block_11))
  (interval_append badTest_13056 96 112 128
  (interval_append badTest_13056 96 104 112
  badTest_13056_block_12
  badTest_13056_block_13)
  (interval_append badTest_13056 112 120 128
  badTest_13056_block_14
  badTest_13056_block_15))))
  (interval_append badTest_13056 128 192 256
  (interval_append badTest_13056 128 160 192
  (interval_append badTest_13056 128 144 160
  (interval_append badTest_13056 128 136 144
  badTest_13056_block_16
  badTest_13056_block_17)
  (interval_append badTest_13056 144 152 160
  badTest_13056_block_18
  badTest_13056_block_19))
  (interval_append badTest_13056 160 176 192
  (interval_append badTest_13056 160 168 176
  badTest_13056_block_20
  badTest_13056_block_21)
  (interval_append badTest_13056 176 184 192
  badTest_13056_block_22
  badTest_13056_block_23)))
  (interval_append badTest_13056 192 224 256
  (interval_append badTest_13056 192 208 224
  (interval_append badTest_13056 192 200 208
  badTest_13056_block_24
  badTest_13056_block_25)
  (interval_append badTest_13056 208 216 224
  badTest_13056_block_26
  badTest_13056_block_27))
  (interval_append badTest_13056 224 240 256
  (interval_append badTest_13056 224 232 240
  badTest_13056_block_28
  badTest_13056_block_29)
  (interval_append badTest_13056 240 248 256
  badTest_13056_block_30
  badTest_13056_block_31)))))
cert_badTestInterval 13056 13312
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad052 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 13312
cert_badTest_block 13312 0 0 8 8
cert_badTest_block 13312 1 8 16 8
cert_badTest_block 13312 2 16 24 8
cert_badTest_block 13312 3 24 32 8
cert_badTest_block 13312 4 32 40 8
cert_badTest_block 13312 5 40 48 8
cert_badTest_block 13312 6 48 56 8
cert_badTest_block 13312 7 56 64 8
cert_badTest_block 13312 8 64 72 8
cert_badTest_block 13312 9 72 80 8
cert_badTest_block 13312 10 80 88 8
cert_badTest_block 13312 11 88 96 8
cert_badTest_block 13312 12 96 104 8
cert_badTest_block 13312 13 104 112 8
cert_badTest_block 13312 14 112 120 8
cert_badTest_block 13312 15 120 128 8
cert_badTest_block 13312 16 128 136 8
cert_badTest_block 13312 17 136 144 8
cert_badTest_block 13312 18 144 152 8
cert_badTest_block 13312 19 152 160 8
cert_badTest_block 13312 20 160 168 8
cert_badTest_block 13312 21 168 176 8
cert_badTest_block 13312 22 176 184 8
cert_badTest_block 13312 23 184 192 8
cert_badTest_block 13312 24 192 200 8
cert_badTest_block 13312 25 200 208 8
cert_badTest_block 13312 26 208 216 8
cert_badTest_block 13312 27 216 224 8
cert_badTest_block 13312 28 224 232 8
cert_badTest_block 13312 29 232 240 8
cert_badTest_block 13312 30 240 248 8
cert_badTest_block 13312 31 248 256 8
theorem badTest_13312_complete : Interval badTest_13312 0 256 :=
  (interval_append badTest_13312 0 128 256
  (interval_append badTest_13312 0 64 128
  (interval_append badTest_13312 0 32 64
  (interval_append badTest_13312 0 16 32
  (interval_append badTest_13312 0 8 16
  badTest_13312_block_0
  badTest_13312_block_1)
  (interval_append badTest_13312 16 24 32
  badTest_13312_block_2
  badTest_13312_block_3))
  (interval_append badTest_13312 32 48 64
  (interval_append badTest_13312 32 40 48
  badTest_13312_block_4
  badTest_13312_block_5)
  (interval_append badTest_13312 48 56 64
  badTest_13312_block_6
  badTest_13312_block_7)))
  (interval_append badTest_13312 64 96 128
  (interval_append badTest_13312 64 80 96
  (interval_append badTest_13312 64 72 80
  badTest_13312_block_8
  badTest_13312_block_9)
  (interval_append badTest_13312 80 88 96
  badTest_13312_block_10
  badTest_13312_block_11))
  (interval_append badTest_13312 96 112 128
  (interval_append badTest_13312 96 104 112
  badTest_13312_block_12
  badTest_13312_block_13)
  (interval_append badTest_13312 112 120 128
  badTest_13312_block_14
  badTest_13312_block_15))))
  (interval_append badTest_13312 128 192 256
  (interval_append badTest_13312 128 160 192
  (interval_append badTest_13312 128 144 160
  (interval_append badTest_13312 128 136 144
  badTest_13312_block_16
  badTest_13312_block_17)
  (interval_append badTest_13312 144 152 160
  badTest_13312_block_18
  badTest_13312_block_19))
  (interval_append badTest_13312 160 176 192
  (interval_append badTest_13312 160 168 176
  badTest_13312_block_20
  badTest_13312_block_21)
  (interval_append badTest_13312 176 184 192
  badTest_13312_block_22
  badTest_13312_block_23)))
  (interval_append badTest_13312 192 224 256
  (interval_append badTest_13312 192 208 224
  (interval_append badTest_13312 192 200 208
  badTest_13312_block_24
  badTest_13312_block_25)
  (interval_append badTest_13312 208 216 224
  badTest_13312_block_26
  badTest_13312_block_27))
  (interval_append badTest_13312 224 240 256
  (interval_append badTest_13312 224 232 240
  badTest_13312_block_28
  badTest_13312_block_29)
  (interval_append badTest_13312 240 248 256
  badTest_13312_block_30
  badTest_13312_block_31)))))
cert_badTestInterval 13312 13568
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad053 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 13568
cert_badTest_block 13568 0 0 8 8
cert_badTest_block 13568 1 8 16 8
cert_badTest_block 13568 2 16 24 8
cert_badTest_block 13568 3 24 32 8
cert_badTest_block 13568 4 32 40 8
cert_badTest_block 13568 5 40 48 8
cert_badTest_block 13568 6 48 56 8
cert_badTest_block 13568 7 56 64 8
cert_badTest_block 13568 8 64 72 8
cert_badTest_block 13568 9 72 80 8
cert_badTest_block 13568 10 80 88 8
cert_badTest_block 13568 11 88 96 8
cert_badTest_block 13568 12 96 104 8
cert_badTest_block 13568 13 104 112 8
cert_badTest_block 13568 14 112 120 8
cert_badTest_block 13568 15 120 128 8
cert_badTest_block 13568 16 128 136 8
cert_badTest_block 13568 17 136 144 8
cert_badTest_block 13568 18 144 152 8
cert_badTest_block 13568 19 152 160 8
cert_badTest_block 13568 20 160 168 8
cert_badTest_block 13568 21 168 176 8
cert_badTest_block 13568 22 176 184 8
cert_badTest_block 13568 23 184 192 8
cert_badTest_block 13568 24 192 200 8
cert_badTest_block 13568 25 200 208 8
cert_badTest_block 13568 26 208 216 8
cert_badTest_block 13568 27 216 224 8
cert_badTest_block 13568 28 224 232 8
cert_badTest_block 13568 29 232 240 8
cert_badTest_block 13568 30 240 248 8
cert_badTest_block 13568 31 248 256 8
theorem badTest_13568_complete : Interval badTest_13568 0 256 :=
  (interval_append badTest_13568 0 128 256
  (interval_append badTest_13568 0 64 128
  (interval_append badTest_13568 0 32 64
  (interval_append badTest_13568 0 16 32
  (interval_append badTest_13568 0 8 16
  badTest_13568_block_0
  badTest_13568_block_1)
  (interval_append badTest_13568 16 24 32
  badTest_13568_block_2
  badTest_13568_block_3))
  (interval_append badTest_13568 32 48 64
  (interval_append badTest_13568 32 40 48
  badTest_13568_block_4
  badTest_13568_block_5)
  (interval_append badTest_13568 48 56 64
  badTest_13568_block_6
  badTest_13568_block_7)))
  (interval_append badTest_13568 64 96 128
  (interval_append badTest_13568 64 80 96
  (interval_append badTest_13568 64 72 80
  badTest_13568_block_8
  badTest_13568_block_9)
  (interval_append badTest_13568 80 88 96
  badTest_13568_block_10
  badTest_13568_block_11))
  (interval_append badTest_13568 96 112 128
  (interval_append badTest_13568 96 104 112
  badTest_13568_block_12
  badTest_13568_block_13)
  (interval_append badTest_13568 112 120 128
  badTest_13568_block_14
  badTest_13568_block_15))))
  (interval_append badTest_13568 128 192 256
  (interval_append badTest_13568 128 160 192
  (interval_append badTest_13568 128 144 160
  (interval_append badTest_13568 128 136 144
  badTest_13568_block_16
  badTest_13568_block_17)
  (interval_append badTest_13568 144 152 160
  badTest_13568_block_18
  badTest_13568_block_19))
  (interval_append badTest_13568 160 176 192
  (interval_append badTest_13568 160 168 176
  badTest_13568_block_20
  badTest_13568_block_21)
  (interval_append badTest_13568 176 184 192
  badTest_13568_block_22
  badTest_13568_block_23)))
  (interval_append badTest_13568 192 224 256
  (interval_append badTest_13568 192 208 224
  (interval_append badTest_13568 192 200 208
  badTest_13568_block_24
  badTest_13568_block_25)
  (interval_append badTest_13568 208 216 224
  badTest_13568_block_26
  badTest_13568_block_27))
  (interval_append badTest_13568 224 240 256
  (interval_append badTest_13568 224 232 240
  badTest_13568_block_28
  badTest_13568_block_29)
  (interval_append badTest_13568 240 248 256
  badTest_13568_block_30
  badTest_13568_block_31)))))
cert_badTestInterval 13568 13824
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad054 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 13824
cert_badTest_block 13824 0 0 8 8
cert_badTest_block 13824 1 8 16 8
cert_badTest_block 13824 2 16 24 8
cert_badTest_block 13824 3 24 32 8
cert_badTest_block 13824 4 32 40 8
cert_badTest_block 13824 5 40 48 8
cert_badTest_block 13824 6 48 56 8
cert_badTest_block 13824 7 56 64 8
cert_badTest_block 13824 8 64 72 8
cert_badTest_block 13824 9 72 80 8
cert_badTest_block 13824 10 80 88 8
cert_badTest_block 13824 11 88 96 8
cert_badTest_block 13824 12 96 104 8
cert_badTest_block 13824 13 104 112 8
cert_badTest_block 13824 14 112 120 8
cert_badTest_block 13824 15 120 128 8
cert_badTest_block 13824 16 128 136 8
cert_badTest_block 13824 17 136 144 8
cert_badTest_block 13824 18 144 152 8
cert_badTest_block 13824 19 152 160 8
cert_badTest_block 13824 20 160 168 8
cert_badTest_block 13824 21 168 176 8
cert_badTest_block 13824 22 176 184 8
cert_badTest_block 13824 23 184 192 8
cert_badTest_block 13824 24 192 200 8
cert_badTest_block 13824 25 200 208 8
cert_badTest_block 13824 26 208 216 8
cert_badTest_block 13824 27 216 224 8
cert_badTest_block 13824 28 224 232 8
cert_badTest_block 13824 29 232 240 8
cert_badTest_block 13824 30 240 248 8
cert_badTest_block 13824 31 248 256 8
theorem badTest_13824_complete : Interval badTest_13824 0 256 :=
  (interval_append badTest_13824 0 128 256
  (interval_append badTest_13824 0 64 128
  (interval_append badTest_13824 0 32 64
  (interval_append badTest_13824 0 16 32
  (interval_append badTest_13824 0 8 16
  badTest_13824_block_0
  badTest_13824_block_1)
  (interval_append badTest_13824 16 24 32
  badTest_13824_block_2
  badTest_13824_block_3))
  (interval_append badTest_13824 32 48 64
  (interval_append badTest_13824 32 40 48
  badTest_13824_block_4
  badTest_13824_block_5)
  (interval_append badTest_13824 48 56 64
  badTest_13824_block_6
  badTest_13824_block_7)))
  (interval_append badTest_13824 64 96 128
  (interval_append badTest_13824 64 80 96
  (interval_append badTest_13824 64 72 80
  badTest_13824_block_8
  badTest_13824_block_9)
  (interval_append badTest_13824 80 88 96
  badTest_13824_block_10
  badTest_13824_block_11))
  (interval_append badTest_13824 96 112 128
  (interval_append badTest_13824 96 104 112
  badTest_13824_block_12
  badTest_13824_block_13)
  (interval_append badTest_13824 112 120 128
  badTest_13824_block_14
  badTest_13824_block_15))))
  (interval_append badTest_13824 128 192 256
  (interval_append badTest_13824 128 160 192
  (interval_append badTest_13824 128 144 160
  (interval_append badTest_13824 128 136 144
  badTest_13824_block_16
  badTest_13824_block_17)
  (interval_append badTest_13824 144 152 160
  badTest_13824_block_18
  badTest_13824_block_19))
  (interval_append badTest_13824 160 176 192
  (interval_append badTest_13824 160 168 176
  badTest_13824_block_20
  badTest_13824_block_21)
  (interval_append badTest_13824 176 184 192
  badTest_13824_block_22
  badTest_13824_block_23)))
  (interval_append badTest_13824 192 224 256
  (interval_append badTest_13824 192 208 224
  (interval_append badTest_13824 192 200 208
  badTest_13824_block_24
  badTest_13824_block_25)
  (interval_append badTest_13824 208 216 224
  badTest_13824_block_26
  badTest_13824_block_27))
  (interval_append badTest_13824 224 240 256
  (interval_append badTest_13824 224 232 240
  badTest_13824_block_28
  badTest_13824_block_29)
  (interval_append badTest_13824 240 248 256
  badTest_13824_block_30
  badTest_13824_block_31)))))
cert_badTestInterval 13824 14080
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad055 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 14080
cert_badTest_block 14080 0 0 8 8
cert_badTest_block 14080 1 8 16 8
cert_badTest_block 14080 2 16 24 8
cert_badTest_block 14080 3 24 32 8
cert_badTest_block 14080 4 32 40 8
cert_badTest_block 14080 5 40 48 8
cert_badTest_block 14080 6 48 56 8
cert_badTest_block 14080 7 56 64 8
cert_badTest_block 14080 8 64 72 8
cert_badTest_block 14080 9 72 80 8
cert_badTest_block 14080 10 80 88 8
cert_badTest_block 14080 11 88 96 8
cert_badTest_block 14080 12 96 104 8
cert_badTest_block 14080 13 104 112 8
cert_badTest_block 14080 14 112 120 8
cert_badTest_block 14080 15 120 128 8
cert_badTest_block 14080 16 128 136 8
cert_badTest_block 14080 17 136 144 8
cert_badTest_block 14080 18 144 152 8
cert_badTest_block 14080 19 152 160 8
cert_badTest_block 14080 20 160 168 8
cert_badTest_block 14080 21 168 176 8
cert_badTest_block 14080 22 176 184 8
cert_badTest_block 14080 23 184 192 8
cert_badTest_block 14080 24 192 200 8
cert_badTest_block 14080 25 200 208 8
cert_badTest_block 14080 26 208 216 8
cert_badTest_block 14080 27 216 224 8
cert_badTest_block 14080 28 224 232 8
cert_badTest_block 14080 29 232 240 8
cert_badTest_block 14080 30 240 248 8
cert_badTest_block 14080 31 248 256 8
theorem badTest_14080_complete : Interval badTest_14080 0 256 :=
  (interval_append badTest_14080 0 128 256
  (interval_append badTest_14080 0 64 128
  (interval_append badTest_14080 0 32 64
  (interval_append badTest_14080 0 16 32
  (interval_append badTest_14080 0 8 16
  badTest_14080_block_0
  badTest_14080_block_1)
  (interval_append badTest_14080 16 24 32
  badTest_14080_block_2
  badTest_14080_block_3))
  (interval_append badTest_14080 32 48 64
  (interval_append badTest_14080 32 40 48
  badTest_14080_block_4
  badTest_14080_block_5)
  (interval_append badTest_14080 48 56 64
  badTest_14080_block_6
  badTest_14080_block_7)))
  (interval_append badTest_14080 64 96 128
  (interval_append badTest_14080 64 80 96
  (interval_append badTest_14080 64 72 80
  badTest_14080_block_8
  badTest_14080_block_9)
  (interval_append badTest_14080 80 88 96
  badTest_14080_block_10
  badTest_14080_block_11))
  (interval_append badTest_14080 96 112 128
  (interval_append badTest_14080 96 104 112
  badTest_14080_block_12
  badTest_14080_block_13)
  (interval_append badTest_14080 112 120 128
  badTest_14080_block_14
  badTest_14080_block_15))))
  (interval_append badTest_14080 128 192 256
  (interval_append badTest_14080 128 160 192
  (interval_append badTest_14080 128 144 160
  (interval_append badTest_14080 128 136 144
  badTest_14080_block_16
  badTest_14080_block_17)
  (interval_append badTest_14080 144 152 160
  badTest_14080_block_18
  badTest_14080_block_19))
  (interval_append badTest_14080 160 176 192
  (interval_append badTest_14080 160 168 176
  badTest_14080_block_20
  badTest_14080_block_21)
  (interval_append badTest_14080 176 184 192
  badTest_14080_block_22
  badTest_14080_block_23)))
  (interval_append badTest_14080 192 224 256
  (interval_append badTest_14080 192 208 224
  (interval_append badTest_14080 192 200 208
  badTest_14080_block_24
  badTest_14080_block_25)
  (interval_append badTest_14080 208 216 224
  badTest_14080_block_26
  badTest_14080_block_27))
  (interval_append badTest_14080 224 240 256
  (interval_append badTest_14080 224 232 240
  badTest_14080_block_28
  badTest_14080_block_29)
  (interval_append badTest_14080 240 248 256
  badTest_14080_block_30
  badTest_14080_block_31)))))
cert_badTestInterval 14080 14336
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad056 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 14336
cert_badTest_block 14336 0 0 8 8
cert_badTest_block 14336 1 8 16 8
cert_badTest_block 14336 2 16 24 8
cert_badTest_block 14336 3 24 32 8
cert_badTest_block 14336 4 32 40 8
cert_badTest_block 14336 5 40 48 8
cert_badTest_block 14336 6 48 56 8
cert_badTest_block 14336 7 56 64 8
cert_badTest_block 14336 8 64 72 8
cert_badTest_block 14336 9 72 80 8
cert_badTest_block 14336 10 80 88 8
cert_badTest_block 14336 11 88 96 8
cert_badTest_block 14336 12 96 104 8
cert_badTest_block 14336 13 104 112 8
cert_badTest_block 14336 14 112 120 8
cert_badTest_block 14336 15 120 128 8
cert_badTest_block 14336 16 128 136 8
cert_badTest_block 14336 17 136 144 8
cert_badTest_block 14336 18 144 152 8
cert_badTest_block 14336 19 152 160 8
cert_badTest_block 14336 20 160 168 8
cert_badTest_block 14336 21 168 176 8
cert_badTest_block 14336 22 176 184 8
cert_badTest_block 14336 23 184 192 8
cert_badTest_block 14336 24 192 200 8
cert_badTest_block 14336 25 200 208 8
cert_badTest_block 14336 26 208 216 8
cert_badTest_block 14336 27 216 224 8
cert_badTest_block 14336 28 224 232 8
cert_badTest_block 14336 29 232 240 8
cert_badTest_block 14336 30 240 248 8
cert_badTest_block 14336 31 248 256 8
theorem badTest_14336_complete : Interval badTest_14336 0 256 :=
  (interval_append badTest_14336 0 128 256
  (interval_append badTest_14336 0 64 128
  (interval_append badTest_14336 0 32 64
  (interval_append badTest_14336 0 16 32
  (interval_append badTest_14336 0 8 16
  badTest_14336_block_0
  badTest_14336_block_1)
  (interval_append badTest_14336 16 24 32
  badTest_14336_block_2
  badTest_14336_block_3))
  (interval_append badTest_14336 32 48 64
  (interval_append badTest_14336 32 40 48
  badTest_14336_block_4
  badTest_14336_block_5)
  (interval_append badTest_14336 48 56 64
  badTest_14336_block_6
  badTest_14336_block_7)))
  (interval_append badTest_14336 64 96 128
  (interval_append badTest_14336 64 80 96
  (interval_append badTest_14336 64 72 80
  badTest_14336_block_8
  badTest_14336_block_9)
  (interval_append badTest_14336 80 88 96
  badTest_14336_block_10
  badTest_14336_block_11))
  (interval_append badTest_14336 96 112 128
  (interval_append badTest_14336 96 104 112
  badTest_14336_block_12
  badTest_14336_block_13)
  (interval_append badTest_14336 112 120 128
  badTest_14336_block_14
  badTest_14336_block_15))))
  (interval_append badTest_14336 128 192 256
  (interval_append badTest_14336 128 160 192
  (interval_append badTest_14336 128 144 160
  (interval_append badTest_14336 128 136 144
  badTest_14336_block_16
  badTest_14336_block_17)
  (interval_append badTest_14336 144 152 160
  badTest_14336_block_18
  badTest_14336_block_19))
  (interval_append badTest_14336 160 176 192
  (interval_append badTest_14336 160 168 176
  badTest_14336_block_20
  badTest_14336_block_21)
  (interval_append badTest_14336 176 184 192
  badTest_14336_block_22
  badTest_14336_block_23)))
  (interval_append badTest_14336 192 224 256
  (interval_append badTest_14336 192 208 224
  (interval_append badTest_14336 192 200 208
  badTest_14336_block_24
  badTest_14336_block_25)
  (interval_append badTest_14336 208 216 224
  badTest_14336_block_26
  badTest_14336_block_27))
  (interval_append badTest_14336 224 240 256
  (interval_append badTest_14336 224 232 240
  badTest_14336_block_28
  badTest_14336_block_29)
  (interval_append badTest_14336 240 248 256
  badTest_14336_block_30
  badTest_14336_block_31)))))
cert_badTestInterval 14336 14592
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad057 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 14592
cert_badTest_block 14592 0 0 8 8
cert_badTest_block 14592 1 8 16 8
cert_badTest_block 14592 2 16 24 8
cert_badTest_block 14592 3 24 32 8
cert_badTest_block 14592 4 32 40 8
cert_badTest_block 14592 5 40 48 8
cert_badTest_block 14592 6 48 56 8
cert_badTest_block 14592 7 56 64 8
cert_badTest_block 14592 8 64 72 8
cert_badTest_block 14592 9 72 80 8
cert_badTest_block 14592 10 80 88 8
cert_badTest_block 14592 11 88 96 8
cert_badTest_block 14592 12 96 104 8
cert_badTest_block 14592 13 104 112 8
cert_badTest_block 14592 14 112 120 8
cert_badTest_block 14592 15 120 128 8
cert_badTest_block 14592 16 128 136 8
cert_badTest_block 14592 17 136 144 8
cert_badTest_block 14592 18 144 152 8
cert_badTest_block 14592 19 152 160 8
cert_badTest_block 14592 20 160 168 8
cert_badTest_block 14592 21 168 176 8
cert_badTest_block 14592 22 176 184 8
cert_badTest_block 14592 23 184 192 8
cert_badTest_block 14592 24 192 200 8
cert_badTest_block 14592 25 200 208 8
cert_badTest_block 14592 26 208 216 8
cert_badTest_block 14592 27 216 224 8
cert_badTest_block 14592 28 224 232 8
cert_badTest_block 14592 29 232 240 8
cert_badTest_block 14592 30 240 248 8
cert_badTest_block 14592 31 248 256 8
theorem badTest_14592_complete : Interval badTest_14592 0 256 :=
  (interval_append badTest_14592 0 128 256
  (interval_append badTest_14592 0 64 128
  (interval_append badTest_14592 0 32 64
  (interval_append badTest_14592 0 16 32
  (interval_append badTest_14592 0 8 16
  badTest_14592_block_0
  badTest_14592_block_1)
  (interval_append badTest_14592 16 24 32
  badTest_14592_block_2
  badTest_14592_block_3))
  (interval_append badTest_14592 32 48 64
  (interval_append badTest_14592 32 40 48
  badTest_14592_block_4
  badTest_14592_block_5)
  (interval_append badTest_14592 48 56 64
  badTest_14592_block_6
  badTest_14592_block_7)))
  (interval_append badTest_14592 64 96 128
  (interval_append badTest_14592 64 80 96
  (interval_append badTest_14592 64 72 80
  badTest_14592_block_8
  badTest_14592_block_9)
  (interval_append badTest_14592 80 88 96
  badTest_14592_block_10
  badTest_14592_block_11))
  (interval_append badTest_14592 96 112 128
  (interval_append badTest_14592 96 104 112
  badTest_14592_block_12
  badTest_14592_block_13)
  (interval_append badTest_14592 112 120 128
  badTest_14592_block_14
  badTest_14592_block_15))))
  (interval_append badTest_14592 128 192 256
  (interval_append badTest_14592 128 160 192
  (interval_append badTest_14592 128 144 160
  (interval_append badTest_14592 128 136 144
  badTest_14592_block_16
  badTest_14592_block_17)
  (interval_append badTest_14592 144 152 160
  badTest_14592_block_18
  badTest_14592_block_19))
  (interval_append badTest_14592 160 176 192
  (interval_append badTest_14592 160 168 176
  badTest_14592_block_20
  badTest_14592_block_21)
  (interval_append badTest_14592 176 184 192
  badTest_14592_block_22
  badTest_14592_block_23)))
  (interval_append badTest_14592 192 224 256
  (interval_append badTest_14592 192 208 224
  (interval_append badTest_14592 192 200 208
  badTest_14592_block_24
  badTest_14592_block_25)
  (interval_append badTest_14592 208 216 224
  badTest_14592_block_26
  badTest_14592_block_27))
  (interval_append badTest_14592 224 240 256
  (interval_append badTest_14592 224 232 240
  badTest_14592_block_28
  badTest_14592_block_29)
  (interval_append badTest_14592 240 248 256
  badTest_14592_block_30
  badTest_14592_block_31)))))
cert_badTestInterval 14592 14848
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
