module
prelude
public meta import LowerSchemas.BundledChecks
public import RootedSixBase01GrowthCacheData

/- RootedSixBase01GrowthCacheBad020 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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
end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad021 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
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
end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad022 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 5632
cert_badTest_block 5632 0 0 8 8
cert_badTest_block 5632 1 8 16 8
cert_badTest_block 5632 2 16 24 8
cert_badTest_block 5632 3 24 32 8
cert_badTest_block 5632 4 32 40 8
cert_badTest_block 5632 5 40 48 8
cert_badTest_block 5632 6 48 56 8
cert_badTest_block 5632 7 56 64 8
cert_badTest_block 5632 8 64 72 8
cert_badTest_block 5632 9 72 80 8
cert_badTest_block 5632 10 80 88 8
cert_badTest_block 5632 11 88 96 8
cert_badTest_block 5632 12 96 104 8
cert_badTest_block 5632 13 104 112 8
cert_badTest_block 5632 14 112 120 8
cert_badTest_block 5632 15 120 128 8
cert_badTest_block 5632 16 128 136 8
cert_badTest_block 5632 17 136 144 8
cert_badTest_block 5632 18 144 152 8
cert_badTest_block 5632 19 152 160 8
cert_badTest_block 5632 20 160 168 8
cert_badTest_block 5632 21 168 176 8
cert_badTest_block 5632 22 176 184 8
cert_badTest_block 5632 23 184 192 8
cert_badTest_block 5632 24 192 200 8
cert_badTest_block 5632 25 200 208 8
cert_badTest_block 5632 26 208 216 8
cert_badTest_block 5632 27 216 224 8
cert_badTest_block 5632 28 224 232 8
cert_badTest_block 5632 29 232 240 8
cert_badTest_block 5632 30 240 248 8
cert_badTest_block 5632 31 248 256 8
theorem badTest_5632_complete : Interval badTest_5632 0 256 :=
  (interval_append badTest_5632 0 128 256
  (interval_append badTest_5632 0 64 128
  (interval_append badTest_5632 0 32 64
  (interval_append badTest_5632 0 16 32
  (interval_append badTest_5632 0 8 16
  badTest_5632_block_0
  badTest_5632_block_1)
  (interval_append badTest_5632 16 24 32
  badTest_5632_block_2
  badTest_5632_block_3))
  (interval_append badTest_5632 32 48 64
  (interval_append badTest_5632 32 40 48
  badTest_5632_block_4
  badTest_5632_block_5)
  (interval_append badTest_5632 48 56 64
  badTest_5632_block_6
  badTest_5632_block_7)))
  (interval_append badTest_5632 64 96 128
  (interval_append badTest_5632 64 80 96
  (interval_append badTest_5632 64 72 80
  badTest_5632_block_8
  badTest_5632_block_9)
  (interval_append badTest_5632 80 88 96
  badTest_5632_block_10
  badTest_5632_block_11))
  (interval_append badTest_5632 96 112 128
  (interval_append badTest_5632 96 104 112
  badTest_5632_block_12
  badTest_5632_block_13)
  (interval_append badTest_5632 112 120 128
  badTest_5632_block_14
  badTest_5632_block_15))))
  (interval_append badTest_5632 128 192 256
  (interval_append badTest_5632 128 160 192
  (interval_append badTest_5632 128 144 160
  (interval_append badTest_5632 128 136 144
  badTest_5632_block_16
  badTest_5632_block_17)
  (interval_append badTest_5632 144 152 160
  badTest_5632_block_18
  badTest_5632_block_19))
  (interval_append badTest_5632 160 176 192
  (interval_append badTest_5632 160 168 176
  badTest_5632_block_20
  badTest_5632_block_21)
  (interval_append badTest_5632 176 184 192
  badTest_5632_block_22
  badTest_5632_block_23)))
  (interval_append badTest_5632 192 224 256
  (interval_append badTest_5632 192 208 224
  (interval_append badTest_5632 192 200 208
  badTest_5632_block_24
  badTest_5632_block_25)
  (interval_append badTest_5632 208 216 224
  badTest_5632_block_26
  badTest_5632_block_27))
  (interval_append badTest_5632 224 240 256
  (interval_append badTest_5632 224 232 240
  badTest_5632_block_28
  badTest_5632_block_29)
  (interval_append badTest_5632 240 248 256
  badTest_5632_block_30
  badTest_5632_block_31)))))
cert_badTestInterval 5632 5888
end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad023 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 5888
cert_badTest_block 5888 0 0 8 8
cert_badTest_block 5888 1 8 16 8
cert_badTest_block 5888 2 16 24 8
cert_badTest_block 5888 3 24 32 8
cert_badTest_block 5888 4 32 40 8
cert_badTest_block 5888 5 40 48 8
cert_badTest_block 5888 6 48 56 8
cert_badTest_block 5888 7 56 64 8
cert_badTest_block 5888 8 64 72 8
cert_badTest_block 5888 9 72 80 8
cert_badTest_block 5888 10 80 88 8
cert_badTest_block 5888 11 88 96 8
cert_badTest_block 5888 12 96 104 8
cert_badTest_block 5888 13 104 112 8
cert_badTest_block 5888 14 112 120 8
cert_badTest_block 5888 15 120 128 8
cert_badTest_block 5888 16 128 136 8
cert_badTest_block 5888 17 136 144 8
cert_badTest_block 5888 18 144 152 8
cert_badTest_block 5888 19 152 160 8
cert_badTest_block 5888 20 160 168 8
cert_badTest_block 5888 21 168 176 8
cert_badTest_block 5888 22 176 184 8
cert_badTest_block 5888 23 184 192 8
cert_badTest_block 5888 24 192 200 8
cert_badTest_block 5888 25 200 208 8
cert_badTest_block 5888 26 208 216 8
cert_badTest_block 5888 27 216 224 8
cert_badTest_block 5888 28 224 232 8
cert_badTest_block 5888 29 232 240 8
cert_badTest_block 5888 30 240 248 8
cert_badTest_block 5888 31 248 256 8
theorem badTest_5888_complete : Interval badTest_5888 0 256 :=
  (interval_append badTest_5888 0 128 256
  (interval_append badTest_5888 0 64 128
  (interval_append badTest_5888 0 32 64
  (interval_append badTest_5888 0 16 32
  (interval_append badTest_5888 0 8 16
  badTest_5888_block_0
  badTest_5888_block_1)
  (interval_append badTest_5888 16 24 32
  badTest_5888_block_2
  badTest_5888_block_3))
  (interval_append badTest_5888 32 48 64
  (interval_append badTest_5888 32 40 48
  badTest_5888_block_4
  badTest_5888_block_5)
  (interval_append badTest_5888 48 56 64
  badTest_5888_block_6
  badTest_5888_block_7)))
  (interval_append badTest_5888 64 96 128
  (interval_append badTest_5888 64 80 96
  (interval_append badTest_5888 64 72 80
  badTest_5888_block_8
  badTest_5888_block_9)
  (interval_append badTest_5888 80 88 96
  badTest_5888_block_10
  badTest_5888_block_11))
  (interval_append badTest_5888 96 112 128
  (interval_append badTest_5888 96 104 112
  badTest_5888_block_12
  badTest_5888_block_13)
  (interval_append badTest_5888 112 120 128
  badTest_5888_block_14
  badTest_5888_block_15))))
  (interval_append badTest_5888 128 192 256
  (interval_append badTest_5888 128 160 192
  (interval_append badTest_5888 128 144 160
  (interval_append badTest_5888 128 136 144
  badTest_5888_block_16
  badTest_5888_block_17)
  (interval_append badTest_5888 144 152 160
  badTest_5888_block_18
  badTest_5888_block_19))
  (interval_append badTest_5888 160 176 192
  (interval_append badTest_5888 160 168 176
  badTest_5888_block_20
  badTest_5888_block_21)
  (interval_append badTest_5888 176 184 192
  badTest_5888_block_22
  badTest_5888_block_23)))
  (interval_append badTest_5888 192 224 256
  (interval_append badTest_5888 192 208 224
  (interval_append badTest_5888 192 200 208
  badTest_5888_block_24
  badTest_5888_block_25)
  (interval_append badTest_5888 208 216 224
  badTest_5888_block_26
  badTest_5888_block_27))
  (interval_append badTest_5888 224 240 256
  (interval_append badTest_5888 224 232 240
  badTest_5888_block_28
  badTest_5888_block_29)
  (interval_append badTest_5888 240 248 256
  badTest_5888_block_30
  badTest_5888_block_31)))))
cert_badTestInterval 5888 6144
end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad024 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 6144
cert_badTest_block 6144 0 0 8 8
cert_badTest_block 6144 1 8 16 8
cert_badTest_block 6144 2 16 24 8
cert_badTest_block 6144 3 24 32 8
cert_badTest_block 6144 4 32 40 8
cert_badTest_block 6144 5 40 48 8
cert_badTest_block 6144 6 48 56 8
cert_badTest_block 6144 7 56 64 8
cert_badTest_block 6144 8 64 72 8
cert_badTest_block 6144 9 72 80 8
cert_badTest_block 6144 10 80 88 8
cert_badTest_block 6144 11 88 96 8
cert_badTest_block 6144 12 96 104 8
cert_badTest_block 6144 13 104 112 8
cert_badTest_block 6144 14 112 120 8
cert_badTest_block 6144 15 120 128 8
cert_badTest_block 6144 16 128 136 8
cert_badTest_block 6144 17 136 144 8
cert_badTest_block 6144 18 144 152 8
cert_badTest_block 6144 19 152 160 8
cert_badTest_block 6144 20 160 168 8
cert_badTest_block 6144 21 168 176 8
cert_badTest_block 6144 22 176 184 8
cert_badTest_block 6144 23 184 192 8
cert_badTest_block 6144 24 192 200 8
cert_badTest_block 6144 25 200 208 8
cert_badTest_block 6144 26 208 216 8
cert_badTest_block 6144 27 216 224 8
cert_badTest_block 6144 28 224 232 8
cert_badTest_block 6144 29 232 240 8
cert_badTest_block 6144 30 240 248 8
cert_badTest_block 6144 31 248 256 8
theorem badTest_6144_complete : Interval badTest_6144 0 256 :=
  (interval_append badTest_6144 0 128 256
  (interval_append badTest_6144 0 64 128
  (interval_append badTest_6144 0 32 64
  (interval_append badTest_6144 0 16 32
  (interval_append badTest_6144 0 8 16
  badTest_6144_block_0
  badTest_6144_block_1)
  (interval_append badTest_6144 16 24 32
  badTest_6144_block_2
  badTest_6144_block_3))
  (interval_append badTest_6144 32 48 64
  (interval_append badTest_6144 32 40 48
  badTest_6144_block_4
  badTest_6144_block_5)
  (interval_append badTest_6144 48 56 64
  badTest_6144_block_6
  badTest_6144_block_7)))
  (interval_append badTest_6144 64 96 128
  (interval_append badTest_6144 64 80 96
  (interval_append badTest_6144 64 72 80
  badTest_6144_block_8
  badTest_6144_block_9)
  (interval_append badTest_6144 80 88 96
  badTest_6144_block_10
  badTest_6144_block_11))
  (interval_append badTest_6144 96 112 128
  (interval_append badTest_6144 96 104 112
  badTest_6144_block_12
  badTest_6144_block_13)
  (interval_append badTest_6144 112 120 128
  badTest_6144_block_14
  badTest_6144_block_15))))
  (interval_append badTest_6144 128 192 256
  (interval_append badTest_6144 128 160 192
  (interval_append badTest_6144 128 144 160
  (interval_append badTest_6144 128 136 144
  badTest_6144_block_16
  badTest_6144_block_17)
  (interval_append badTest_6144 144 152 160
  badTest_6144_block_18
  badTest_6144_block_19))
  (interval_append badTest_6144 160 176 192
  (interval_append badTest_6144 160 168 176
  badTest_6144_block_20
  badTest_6144_block_21)
  (interval_append badTest_6144 176 184 192
  badTest_6144_block_22
  badTest_6144_block_23)))
  (interval_append badTest_6144 192 224 256
  (interval_append badTest_6144 192 208 224
  (interval_append badTest_6144 192 200 208
  badTest_6144_block_24
  badTest_6144_block_25)
  (interval_append badTest_6144 208 216 224
  badTest_6144_block_26
  badTest_6144_block_27))
  (interval_append badTest_6144 224 240 256
  (interval_append badTest_6144 224 232 240
  badTest_6144_block_28
  badTest_6144_block_29)
  (interval_append badTest_6144 240 248 256
  badTest_6144_block_30
  badTest_6144_block_31)))))
cert_badTestInterval 6144 6400
end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad025 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 6400
cert_badTest_block 6400 0 0 8 8
cert_badTest_block 6400 1 8 16 8
cert_badTest_block 6400 2 16 24 8
cert_badTest_block 6400 3 24 32 8
cert_badTest_block 6400 4 32 40 8
cert_badTest_block 6400 5 40 48 8
cert_badTest_block 6400 6 48 56 8
cert_badTest_block 6400 7 56 64 8
cert_badTest_block 6400 8 64 72 8
cert_badTest_block 6400 9 72 80 8
cert_badTest_block 6400 10 80 88 8
cert_badTest_block 6400 11 88 96 8
cert_badTest_block 6400 12 96 104 8
cert_badTest_block 6400 13 104 112 8
cert_badTest_block 6400 14 112 120 8
cert_badTest_block 6400 15 120 128 8
cert_badTest_block 6400 16 128 136 8
cert_badTest_block 6400 17 136 144 8
cert_badTest_block 6400 18 144 152 8
cert_badTest_block 6400 19 152 160 8
cert_badTest_block 6400 20 160 168 8
cert_badTest_block 6400 21 168 176 8
cert_badTest_block 6400 22 176 184 8
cert_badTest_block 6400 23 184 192 8
cert_badTest_block 6400 24 192 200 8
cert_badTest_block 6400 25 200 208 8
cert_badTest_block 6400 26 208 216 8
cert_badTest_block 6400 27 216 224 8
cert_badTest_block 6400 28 224 232 8
cert_badTest_block 6400 29 232 240 8
cert_badTest_block 6400 30 240 248 8
cert_badTest_block 6400 31 248 256 8
theorem badTest_6400_complete : Interval badTest_6400 0 256 :=
  (interval_append badTest_6400 0 128 256
  (interval_append badTest_6400 0 64 128
  (interval_append badTest_6400 0 32 64
  (interval_append badTest_6400 0 16 32
  (interval_append badTest_6400 0 8 16
  badTest_6400_block_0
  badTest_6400_block_1)
  (interval_append badTest_6400 16 24 32
  badTest_6400_block_2
  badTest_6400_block_3))
  (interval_append badTest_6400 32 48 64
  (interval_append badTest_6400 32 40 48
  badTest_6400_block_4
  badTest_6400_block_5)
  (interval_append badTest_6400 48 56 64
  badTest_6400_block_6
  badTest_6400_block_7)))
  (interval_append badTest_6400 64 96 128
  (interval_append badTest_6400 64 80 96
  (interval_append badTest_6400 64 72 80
  badTest_6400_block_8
  badTest_6400_block_9)
  (interval_append badTest_6400 80 88 96
  badTest_6400_block_10
  badTest_6400_block_11))
  (interval_append badTest_6400 96 112 128
  (interval_append badTest_6400 96 104 112
  badTest_6400_block_12
  badTest_6400_block_13)
  (interval_append badTest_6400 112 120 128
  badTest_6400_block_14
  badTest_6400_block_15))))
  (interval_append badTest_6400 128 192 256
  (interval_append badTest_6400 128 160 192
  (interval_append badTest_6400 128 144 160
  (interval_append badTest_6400 128 136 144
  badTest_6400_block_16
  badTest_6400_block_17)
  (interval_append badTest_6400 144 152 160
  badTest_6400_block_18
  badTest_6400_block_19))
  (interval_append badTest_6400 160 176 192
  (interval_append badTest_6400 160 168 176
  badTest_6400_block_20
  badTest_6400_block_21)
  (interval_append badTest_6400 176 184 192
  badTest_6400_block_22
  badTest_6400_block_23)))
  (interval_append badTest_6400 192 224 256
  (interval_append badTest_6400 192 208 224
  (interval_append badTest_6400 192 200 208
  badTest_6400_block_24
  badTest_6400_block_25)
  (interval_append badTest_6400 208 216 224
  badTest_6400_block_26
  badTest_6400_block_27))
  (interval_append badTest_6400 224 240 256
  (interval_append badTest_6400 224 232 240
  badTest_6400_block_28
  badTest_6400_block_29)
  (interval_append badTest_6400 240 248 256
  badTest_6400_block_30
  badTest_6400_block_31)))))
cert_badTestInterval 6400 6656
end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad026 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 6656
cert_badTest_block 6656 0 0 8 8
cert_badTest_block 6656 1 8 16 8
cert_badTest_block 6656 2 16 24 8
cert_badTest_block 6656 3 24 32 8
cert_badTest_block 6656 4 32 40 8
cert_badTest_block 6656 5 40 48 8
cert_badTest_block 6656 6 48 56 8
cert_badTest_block 6656 7 56 64 8
cert_badTest_block 6656 8 64 72 8
cert_badTest_block 6656 9 72 80 8
cert_badTest_block 6656 10 80 88 8
cert_badTest_block 6656 11 88 96 8
cert_badTest_block 6656 12 96 104 8
cert_badTest_block 6656 13 104 112 8
cert_badTest_block 6656 14 112 120 8
cert_badTest_block 6656 15 120 128 8
cert_badTest_block 6656 16 128 136 8
cert_badTest_block 6656 17 136 144 8
cert_badTest_block 6656 18 144 152 8
cert_badTest_block 6656 19 152 160 8
cert_badTest_block 6656 20 160 168 8
cert_badTest_block 6656 21 168 176 8
cert_badTest_block 6656 22 176 184 8
cert_badTest_block 6656 23 184 192 8
cert_badTest_block 6656 24 192 200 8
cert_badTest_block 6656 25 200 208 8
cert_badTest_block 6656 26 208 216 8
cert_badTest_block 6656 27 216 224 8
cert_badTest_block 6656 28 224 232 8
cert_badTest_block 6656 29 232 240 8
cert_badTest_block 6656 30 240 248 8
cert_badTest_block 6656 31 248 256 8
theorem badTest_6656_complete : Interval badTest_6656 0 256 :=
  (interval_append badTest_6656 0 128 256
  (interval_append badTest_6656 0 64 128
  (interval_append badTest_6656 0 32 64
  (interval_append badTest_6656 0 16 32
  (interval_append badTest_6656 0 8 16
  badTest_6656_block_0
  badTest_6656_block_1)
  (interval_append badTest_6656 16 24 32
  badTest_6656_block_2
  badTest_6656_block_3))
  (interval_append badTest_6656 32 48 64
  (interval_append badTest_6656 32 40 48
  badTest_6656_block_4
  badTest_6656_block_5)
  (interval_append badTest_6656 48 56 64
  badTest_6656_block_6
  badTest_6656_block_7)))
  (interval_append badTest_6656 64 96 128
  (interval_append badTest_6656 64 80 96
  (interval_append badTest_6656 64 72 80
  badTest_6656_block_8
  badTest_6656_block_9)
  (interval_append badTest_6656 80 88 96
  badTest_6656_block_10
  badTest_6656_block_11))
  (interval_append badTest_6656 96 112 128
  (interval_append badTest_6656 96 104 112
  badTest_6656_block_12
  badTest_6656_block_13)
  (interval_append badTest_6656 112 120 128
  badTest_6656_block_14
  badTest_6656_block_15))))
  (interval_append badTest_6656 128 192 256
  (interval_append badTest_6656 128 160 192
  (interval_append badTest_6656 128 144 160
  (interval_append badTest_6656 128 136 144
  badTest_6656_block_16
  badTest_6656_block_17)
  (interval_append badTest_6656 144 152 160
  badTest_6656_block_18
  badTest_6656_block_19))
  (interval_append badTest_6656 160 176 192
  (interval_append badTest_6656 160 168 176
  badTest_6656_block_20
  badTest_6656_block_21)
  (interval_append badTest_6656 176 184 192
  badTest_6656_block_22
  badTest_6656_block_23)))
  (interval_append badTest_6656 192 224 256
  (interval_append badTest_6656 192 208 224
  (interval_append badTest_6656 192 200 208
  badTest_6656_block_24
  badTest_6656_block_25)
  (interval_append badTest_6656 208 216 224
  badTest_6656_block_26
  badTest_6656_block_27))
  (interval_append badTest_6656 224 240 256
  (interval_append badTest_6656 224 232 240
  badTest_6656_block_28
  badTest_6656_block_29)
  (interval_append badTest_6656 240 248 256
  badTest_6656_block_30
  badTest_6656_block_31)))))
cert_badTestInterval 6656 6912
end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad027 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 6912
cert_badTest_block 6912 0 0 8 8
cert_badTest_block 6912 1 8 16 8
cert_badTest_block 6912 2 16 24 8
cert_badTest_block 6912 3 24 32 8
cert_badTest_block 6912 4 32 40 8
cert_badTest_block 6912 5 40 48 8
cert_badTest_block 6912 6 48 56 8
cert_badTest_block 6912 7 56 64 8
cert_badTest_block 6912 8 64 72 8
cert_badTest_block 6912 9 72 80 8
cert_badTest_block 6912 10 80 88 8
cert_badTest_block 6912 11 88 96 8
cert_badTest_block 6912 12 96 104 8
cert_badTest_block 6912 13 104 112 8
cert_badTest_block 6912 14 112 120 8
cert_badTest_block 6912 15 120 128 8
cert_badTest_block 6912 16 128 136 8
cert_badTest_block 6912 17 136 144 8
cert_badTest_block 6912 18 144 152 8
cert_badTest_block 6912 19 152 160 8
cert_badTest_block 6912 20 160 168 8
cert_badTest_block 6912 21 168 176 8
cert_badTest_block 6912 22 176 184 8
cert_badTest_block 6912 23 184 192 8
cert_badTest_block 6912 24 192 200 8
cert_badTest_block 6912 25 200 208 8
cert_badTest_block 6912 26 208 216 8
cert_badTest_block 6912 27 216 224 8
cert_badTest_block 6912 28 224 232 8
cert_badTest_block 6912 29 232 240 8
cert_badTest_block 6912 30 240 248 8
cert_badTest_block 6912 31 248 256 8
theorem badTest_6912_complete : Interval badTest_6912 0 256 :=
  (interval_append badTest_6912 0 128 256
  (interval_append badTest_6912 0 64 128
  (interval_append badTest_6912 0 32 64
  (interval_append badTest_6912 0 16 32
  (interval_append badTest_6912 0 8 16
  badTest_6912_block_0
  badTest_6912_block_1)
  (interval_append badTest_6912 16 24 32
  badTest_6912_block_2
  badTest_6912_block_3))
  (interval_append badTest_6912 32 48 64
  (interval_append badTest_6912 32 40 48
  badTest_6912_block_4
  badTest_6912_block_5)
  (interval_append badTest_6912 48 56 64
  badTest_6912_block_6
  badTest_6912_block_7)))
  (interval_append badTest_6912 64 96 128
  (interval_append badTest_6912 64 80 96
  (interval_append badTest_6912 64 72 80
  badTest_6912_block_8
  badTest_6912_block_9)
  (interval_append badTest_6912 80 88 96
  badTest_6912_block_10
  badTest_6912_block_11))
  (interval_append badTest_6912 96 112 128
  (interval_append badTest_6912 96 104 112
  badTest_6912_block_12
  badTest_6912_block_13)
  (interval_append badTest_6912 112 120 128
  badTest_6912_block_14
  badTest_6912_block_15))))
  (interval_append badTest_6912 128 192 256
  (interval_append badTest_6912 128 160 192
  (interval_append badTest_6912 128 144 160
  (interval_append badTest_6912 128 136 144
  badTest_6912_block_16
  badTest_6912_block_17)
  (interval_append badTest_6912 144 152 160
  badTest_6912_block_18
  badTest_6912_block_19))
  (interval_append badTest_6912 160 176 192
  (interval_append badTest_6912 160 168 176
  badTest_6912_block_20
  badTest_6912_block_21)
  (interval_append badTest_6912 176 184 192
  badTest_6912_block_22
  badTest_6912_block_23)))
  (interval_append badTest_6912 192 224 256
  (interval_append badTest_6912 192 208 224
  (interval_append badTest_6912 192 200 208
  badTest_6912_block_24
  badTest_6912_block_25)
  (interval_append badTest_6912 208 216 224
  badTest_6912_block_26
  badTest_6912_block_27))
  (interval_append badTest_6912 224 240 256
  (interval_append badTest_6912 224 232 240
  badTest_6912_block_28
  badTest_6912_block_29)
  (interval_append badTest_6912 240 248 256
  badTest_6912_block_30
  badTest_6912_block_31)))))
cert_badTestInterval 6912 7168
end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad028 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 7168
cert_badTest_block 7168 0 0 8 8
cert_badTest_block 7168 1 8 16 8
cert_badTest_block 7168 2 16 24 8
cert_badTest_block 7168 3 24 32 8
cert_badTest_block 7168 4 32 40 8
cert_badTest_block 7168 5 40 48 8
cert_badTest_block 7168 6 48 56 8
cert_badTest_block 7168 7 56 64 8
cert_badTest_block 7168 8 64 72 8
cert_badTest_block 7168 9 72 80 8
cert_badTest_block 7168 10 80 88 8
cert_badTest_block 7168 11 88 96 8
cert_badTest_block 7168 12 96 104 8
cert_badTest_block 7168 13 104 112 8
cert_badTest_block 7168 14 112 120 8
cert_badTest_block 7168 15 120 128 8
cert_badTest_block 7168 16 128 136 8
cert_badTest_block 7168 17 136 144 8
cert_badTest_block 7168 18 144 152 8
cert_badTest_block 7168 19 152 160 8
cert_badTest_block 7168 20 160 168 8
cert_badTest_block 7168 21 168 176 8
cert_badTest_block 7168 22 176 184 8
cert_badTest_block 7168 23 184 192 8
cert_badTest_block 7168 24 192 200 8
cert_badTest_block 7168 25 200 208 8
cert_badTest_block 7168 26 208 216 8
cert_badTest_block 7168 27 216 224 8
cert_badTest_block 7168 28 224 232 8
cert_badTest_block 7168 29 232 240 8
cert_badTest_block 7168 30 240 248 8
cert_badTest_block 7168 31 248 256 8
theorem badTest_7168_complete : Interval badTest_7168 0 256 :=
  (interval_append badTest_7168 0 128 256
  (interval_append badTest_7168 0 64 128
  (interval_append badTest_7168 0 32 64
  (interval_append badTest_7168 0 16 32
  (interval_append badTest_7168 0 8 16
  badTest_7168_block_0
  badTest_7168_block_1)
  (interval_append badTest_7168 16 24 32
  badTest_7168_block_2
  badTest_7168_block_3))
  (interval_append badTest_7168 32 48 64
  (interval_append badTest_7168 32 40 48
  badTest_7168_block_4
  badTest_7168_block_5)
  (interval_append badTest_7168 48 56 64
  badTest_7168_block_6
  badTest_7168_block_7)))
  (interval_append badTest_7168 64 96 128
  (interval_append badTest_7168 64 80 96
  (interval_append badTest_7168 64 72 80
  badTest_7168_block_8
  badTest_7168_block_9)
  (interval_append badTest_7168 80 88 96
  badTest_7168_block_10
  badTest_7168_block_11))
  (interval_append badTest_7168 96 112 128
  (interval_append badTest_7168 96 104 112
  badTest_7168_block_12
  badTest_7168_block_13)
  (interval_append badTest_7168 112 120 128
  badTest_7168_block_14
  badTest_7168_block_15))))
  (interval_append badTest_7168 128 192 256
  (interval_append badTest_7168 128 160 192
  (interval_append badTest_7168 128 144 160
  (interval_append badTest_7168 128 136 144
  badTest_7168_block_16
  badTest_7168_block_17)
  (interval_append badTest_7168 144 152 160
  badTest_7168_block_18
  badTest_7168_block_19))
  (interval_append badTest_7168 160 176 192
  (interval_append badTest_7168 160 168 176
  badTest_7168_block_20
  badTest_7168_block_21)
  (interval_append badTest_7168 176 184 192
  badTest_7168_block_22
  badTest_7168_block_23)))
  (interval_append badTest_7168 192 224 256
  (interval_append badTest_7168 192 208 224
  (interval_append badTest_7168 192 200 208
  badTest_7168_block_24
  badTest_7168_block_25)
  (interval_append badTest_7168 208 216 224
  badTest_7168_block_26
  badTest_7168_block_27))
  (interval_append badTest_7168 224 240 256
  (interval_append badTest_7168 224 232 240
  badTest_7168_block_28
  badTest_7168_block_29)
  (interval_append badTest_7168 240 248 256
  badTest_7168_block_30
  badTest_7168_block_31)))))
cert_badTestInterval 7168 7424
end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad029 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 7424
cert_badTest_block 7424 0 0 8 8
cert_badTest_block 7424 1 8 16 8
cert_badTest_block 7424 2 16 24 8
cert_badTest_block 7424 3 24 32 8
cert_badTest_block 7424 4 32 40 8
cert_badTest_block 7424 5 40 48 8
cert_badTest_block 7424 6 48 56 8
cert_badTest_block 7424 7 56 64 8
cert_badTest_block 7424 8 64 72 8
cert_badTest_block 7424 9 72 80 8
cert_badTest_block 7424 10 80 88 8
cert_badTest_block 7424 11 88 96 8
cert_badTest_block 7424 12 96 104 8
cert_badTest_block 7424 13 104 112 8
cert_badTest_block 7424 14 112 120 8
cert_badTest_block 7424 15 120 128 8
cert_badTest_block 7424 16 128 136 8
cert_badTest_block 7424 17 136 144 8
cert_badTest_block 7424 18 144 152 8
cert_badTest_block 7424 19 152 160 8
cert_badTest_block 7424 20 160 168 8
cert_badTest_block 7424 21 168 176 8
cert_badTest_block 7424 22 176 184 8
cert_badTest_block 7424 23 184 192 8
cert_badTest_block 7424 24 192 200 8
cert_badTest_block 7424 25 200 208 8
cert_badTest_block 7424 26 208 216 8
cert_badTest_block 7424 27 216 224 8
cert_badTest_block 7424 28 224 232 8
cert_badTest_block 7424 29 232 240 8
cert_badTest_block 7424 30 240 248 8
cert_badTest_block 7424 31 248 256 8
theorem badTest_7424_complete : Interval badTest_7424 0 256 :=
  (interval_append badTest_7424 0 128 256
  (interval_append badTest_7424 0 64 128
  (interval_append badTest_7424 0 32 64
  (interval_append badTest_7424 0 16 32
  (interval_append badTest_7424 0 8 16
  badTest_7424_block_0
  badTest_7424_block_1)
  (interval_append badTest_7424 16 24 32
  badTest_7424_block_2
  badTest_7424_block_3))
  (interval_append badTest_7424 32 48 64
  (interval_append badTest_7424 32 40 48
  badTest_7424_block_4
  badTest_7424_block_5)
  (interval_append badTest_7424 48 56 64
  badTest_7424_block_6
  badTest_7424_block_7)))
  (interval_append badTest_7424 64 96 128
  (interval_append badTest_7424 64 80 96
  (interval_append badTest_7424 64 72 80
  badTest_7424_block_8
  badTest_7424_block_9)
  (interval_append badTest_7424 80 88 96
  badTest_7424_block_10
  badTest_7424_block_11))
  (interval_append badTest_7424 96 112 128
  (interval_append badTest_7424 96 104 112
  badTest_7424_block_12
  badTest_7424_block_13)
  (interval_append badTest_7424 112 120 128
  badTest_7424_block_14
  badTest_7424_block_15))))
  (interval_append badTest_7424 128 192 256
  (interval_append badTest_7424 128 160 192
  (interval_append badTest_7424 128 144 160
  (interval_append badTest_7424 128 136 144
  badTest_7424_block_16
  badTest_7424_block_17)
  (interval_append badTest_7424 144 152 160
  badTest_7424_block_18
  badTest_7424_block_19))
  (interval_append badTest_7424 160 176 192
  (interval_append badTest_7424 160 168 176
  badTest_7424_block_20
  badTest_7424_block_21)
  (interval_append badTest_7424 176 184 192
  badTest_7424_block_22
  badTest_7424_block_23)))
  (interval_append badTest_7424 192 224 256
  (interval_append badTest_7424 192 208 224
  (interval_append badTest_7424 192 200 208
  badTest_7424_block_24
  badTest_7424_block_25)
  (interval_append badTest_7424 208 216 224
  badTest_7424_block_26
  badTest_7424_block_27))
  (interval_append badTest_7424 224 240 256
  (interval_append badTest_7424 224 232 240
  badTest_7424_block_28
  badTest_7424_block_29)
  (interval_append badTest_7424 240 248 256
  badTest_7424_block_30
  badTest_7424_block_31)))))
cert_badTestInterval 7424 7680
end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad030 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 7680
cert_badTest_block 7680 0 0 8 8
cert_badTest_block 7680 1 8 16 8
cert_badTest_block 7680 2 16 24 8
cert_badTest_block 7680 3 24 32 8
cert_badTest_block 7680 4 32 40 8
cert_badTest_block 7680 5 40 48 8
cert_badTest_block 7680 6 48 56 8
cert_badTest_block 7680 7 56 64 8
cert_badTest_block 7680 8 64 72 8
cert_badTest_block 7680 9 72 80 8
cert_badTest_block 7680 10 80 88 8
cert_badTest_block 7680 11 88 96 8
cert_badTest_block 7680 12 96 104 8
cert_badTest_block 7680 13 104 112 8
cert_badTest_block 7680 14 112 120 8
cert_badTest_block 7680 15 120 128 8
cert_badTest_block 7680 16 128 136 8
cert_badTest_block 7680 17 136 144 8
cert_badTest_block 7680 18 144 152 8
cert_badTest_block 7680 19 152 160 8
cert_badTest_block 7680 20 160 168 8
cert_badTest_block 7680 21 168 176 8
cert_badTest_block 7680 22 176 184 8
cert_badTest_block 7680 23 184 192 8
cert_badTest_block 7680 24 192 200 8
cert_badTest_block 7680 25 200 208 8
cert_badTest_block 7680 26 208 216 8
cert_badTest_block 7680 27 216 224 8
cert_badTest_block 7680 28 224 232 8
cert_badTest_block 7680 29 232 240 8
cert_badTest_block 7680 30 240 248 8
cert_badTest_block 7680 31 248 256 8
theorem badTest_7680_complete : Interval badTest_7680 0 256 :=
  (interval_append badTest_7680 0 128 256
  (interval_append badTest_7680 0 64 128
  (interval_append badTest_7680 0 32 64
  (interval_append badTest_7680 0 16 32
  (interval_append badTest_7680 0 8 16
  badTest_7680_block_0
  badTest_7680_block_1)
  (interval_append badTest_7680 16 24 32
  badTest_7680_block_2
  badTest_7680_block_3))
  (interval_append badTest_7680 32 48 64
  (interval_append badTest_7680 32 40 48
  badTest_7680_block_4
  badTest_7680_block_5)
  (interval_append badTest_7680 48 56 64
  badTest_7680_block_6
  badTest_7680_block_7)))
  (interval_append badTest_7680 64 96 128
  (interval_append badTest_7680 64 80 96
  (interval_append badTest_7680 64 72 80
  badTest_7680_block_8
  badTest_7680_block_9)
  (interval_append badTest_7680 80 88 96
  badTest_7680_block_10
  badTest_7680_block_11))
  (interval_append badTest_7680 96 112 128
  (interval_append badTest_7680 96 104 112
  badTest_7680_block_12
  badTest_7680_block_13)
  (interval_append badTest_7680 112 120 128
  badTest_7680_block_14
  badTest_7680_block_15))))
  (interval_append badTest_7680 128 192 256
  (interval_append badTest_7680 128 160 192
  (interval_append badTest_7680 128 144 160
  (interval_append badTest_7680 128 136 144
  badTest_7680_block_16
  badTest_7680_block_17)
  (interval_append badTest_7680 144 152 160
  badTest_7680_block_18
  badTest_7680_block_19))
  (interval_append badTest_7680 160 176 192
  (interval_append badTest_7680 160 168 176
  badTest_7680_block_20
  badTest_7680_block_21)
  (interval_append badTest_7680 176 184 192
  badTest_7680_block_22
  badTest_7680_block_23)))
  (interval_append badTest_7680 192 224 256
  (interval_append badTest_7680 192 208 224
  (interval_append badTest_7680 192 200 208
  badTest_7680_block_24
  badTest_7680_block_25)
  (interval_append badTest_7680 208 216 224
  badTest_7680_block_26
  badTest_7680_block_27))
  (interval_append badTest_7680 224 240 256
  (interval_append badTest_7680 224 232 240
  badTest_7680_block_28
  badTest_7680_block_29)
  (interval_append badTest_7680 240 248 256
  badTest_7680_block_30
  badTest_7680_block_31)))))
cert_badTestInterval 7680 7936
end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad031 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 7936
cert_badTest_block 7936 0 0 8 8
cert_badTest_block 7936 1 8 16 8
cert_badTest_block 7936 2 16 24 8
cert_badTest_block 7936 3 24 32 8
cert_badTest_block 7936 4 32 40 8
cert_badTest_block 7936 5 40 48 8
cert_badTest_block 7936 6 48 56 8
cert_badTest_block 7936 7 56 64 8
cert_badTest_block 7936 8 64 72 8
cert_badTest_block 7936 9 72 80 8
cert_badTest_block 7936 10 80 88 8
cert_badTest_block 7936 11 88 96 8
cert_badTest_block 7936 12 96 104 8
cert_badTest_block 7936 13 104 112 8
cert_badTest_block 7936 14 112 120 8
cert_badTest_block 7936 15 120 128 8
cert_badTest_block 7936 16 128 136 8
cert_badTest_block 7936 17 136 144 8
cert_badTest_block 7936 18 144 152 8
cert_badTest_block 7936 19 152 160 8
cert_badTest_block 7936 20 160 168 8
cert_badTest_block 7936 21 168 176 8
cert_badTest_block 7936 22 176 184 8
cert_badTest_block 7936 23 184 192 8
cert_badTest_block 7936 24 192 200 8
cert_badTest_block 7936 25 200 208 8
cert_badTest_block 7936 26 208 216 8
cert_badTest_block 7936 27 216 224 8
cert_badTest_block 7936 28 224 232 8
cert_badTest_block 7936 29 232 240 8
cert_badTest_block 7936 30 240 248 8
cert_badTest_block 7936 31 248 256 8
theorem badTest_7936_complete : Interval badTest_7936 0 256 :=
  (interval_append badTest_7936 0 128 256
  (interval_append badTest_7936 0 64 128
  (interval_append badTest_7936 0 32 64
  (interval_append badTest_7936 0 16 32
  (interval_append badTest_7936 0 8 16
  badTest_7936_block_0
  badTest_7936_block_1)
  (interval_append badTest_7936 16 24 32
  badTest_7936_block_2
  badTest_7936_block_3))
  (interval_append badTest_7936 32 48 64
  (interval_append badTest_7936 32 40 48
  badTest_7936_block_4
  badTest_7936_block_5)
  (interval_append badTest_7936 48 56 64
  badTest_7936_block_6
  badTest_7936_block_7)))
  (interval_append badTest_7936 64 96 128
  (interval_append badTest_7936 64 80 96
  (interval_append badTest_7936 64 72 80
  badTest_7936_block_8
  badTest_7936_block_9)
  (interval_append badTest_7936 80 88 96
  badTest_7936_block_10
  badTest_7936_block_11))
  (interval_append badTest_7936 96 112 128
  (interval_append badTest_7936 96 104 112
  badTest_7936_block_12
  badTest_7936_block_13)
  (interval_append badTest_7936 112 120 128
  badTest_7936_block_14
  badTest_7936_block_15))))
  (interval_append badTest_7936 128 192 256
  (interval_append badTest_7936 128 160 192
  (interval_append badTest_7936 128 144 160
  (interval_append badTest_7936 128 136 144
  badTest_7936_block_16
  badTest_7936_block_17)
  (interval_append badTest_7936 144 152 160
  badTest_7936_block_18
  badTest_7936_block_19))
  (interval_append badTest_7936 160 176 192
  (interval_append badTest_7936 160 168 176
  badTest_7936_block_20
  badTest_7936_block_21)
  (interval_append badTest_7936 176 184 192
  badTest_7936_block_22
  badTest_7936_block_23)))
  (interval_append badTest_7936 192 224 256
  (interval_append badTest_7936 192 208 224
  (interval_append badTest_7936 192 200 208
  badTest_7936_block_24
  badTest_7936_block_25)
  (interval_append badTest_7936 208 216 224
  badTest_7936_block_26
  badTest_7936_block_27))
  (interval_append badTest_7936 224 240 256
  (interval_append badTest_7936 224 232 240
  badTest_7936_block_28
  badTest_7936_block_29)
  (interval_append badTest_7936 240 248 256
  badTest_7936_block_30
  badTest_7936_block_31)))))
cert_badTestInterval 7936 8192
end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad032 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 8192
cert_badTest_block 8192 0 0 8 8
cert_badTest_block 8192 1 8 16 8
cert_badTest_block 8192 2 16 24 8
cert_badTest_block 8192 3 24 32 8
cert_badTest_block 8192 4 32 40 8
cert_badTest_block 8192 5 40 48 8
cert_badTest_block 8192 6 48 56 8
cert_badTest_block 8192 7 56 64 8
cert_badTest_block 8192 8 64 72 8
cert_badTest_block 8192 9 72 80 8
cert_badTest_block 8192 10 80 88 8
cert_badTest_block 8192 11 88 96 8
cert_badTest_block 8192 12 96 104 8
cert_badTest_block 8192 13 104 112 8
cert_badTest_block 8192 14 112 120 8
cert_badTest_block 8192 15 120 128 8
cert_badTest_block 8192 16 128 136 8
cert_badTest_block 8192 17 136 144 8
cert_badTest_block 8192 18 144 152 8
cert_badTest_block 8192 19 152 160 8
cert_badTest_block 8192 20 160 168 8
cert_badTest_block 8192 21 168 176 8
cert_badTest_block 8192 22 176 184 8
cert_badTest_block 8192 23 184 192 8
cert_badTest_block 8192 24 192 200 8
cert_badTest_block 8192 25 200 208 8
cert_badTest_block 8192 26 208 216 8
cert_badTest_block 8192 27 216 224 8
cert_badTest_block 8192 28 224 232 8
cert_badTest_block 8192 29 232 240 8
cert_badTest_block 8192 30 240 248 8
cert_badTest_block 8192 31 248 256 8
theorem badTest_8192_complete : Interval badTest_8192 0 256 :=
  (interval_append badTest_8192 0 128 256
  (interval_append badTest_8192 0 64 128
  (interval_append badTest_8192 0 32 64
  (interval_append badTest_8192 0 16 32
  (interval_append badTest_8192 0 8 16
  badTest_8192_block_0
  badTest_8192_block_1)
  (interval_append badTest_8192 16 24 32
  badTest_8192_block_2
  badTest_8192_block_3))
  (interval_append badTest_8192 32 48 64
  (interval_append badTest_8192 32 40 48
  badTest_8192_block_4
  badTest_8192_block_5)
  (interval_append badTest_8192 48 56 64
  badTest_8192_block_6
  badTest_8192_block_7)))
  (interval_append badTest_8192 64 96 128
  (interval_append badTest_8192 64 80 96
  (interval_append badTest_8192 64 72 80
  badTest_8192_block_8
  badTest_8192_block_9)
  (interval_append badTest_8192 80 88 96
  badTest_8192_block_10
  badTest_8192_block_11))
  (interval_append badTest_8192 96 112 128
  (interval_append badTest_8192 96 104 112
  badTest_8192_block_12
  badTest_8192_block_13)
  (interval_append badTest_8192 112 120 128
  badTest_8192_block_14
  badTest_8192_block_15))))
  (interval_append badTest_8192 128 192 256
  (interval_append badTest_8192 128 160 192
  (interval_append badTest_8192 128 144 160
  (interval_append badTest_8192 128 136 144
  badTest_8192_block_16
  badTest_8192_block_17)
  (interval_append badTest_8192 144 152 160
  badTest_8192_block_18
  badTest_8192_block_19))
  (interval_append badTest_8192 160 176 192
  (interval_append badTest_8192 160 168 176
  badTest_8192_block_20
  badTest_8192_block_21)
  (interval_append badTest_8192 176 184 192
  badTest_8192_block_22
  badTest_8192_block_23)))
  (interval_append badTest_8192 192 224 256
  (interval_append badTest_8192 192 208 224
  (interval_append badTest_8192 192 200 208
  badTest_8192_block_24
  badTest_8192_block_25)
  (interval_append badTest_8192 208 216 224
  badTest_8192_block_26
  badTest_8192_block_27))
  (interval_append badTest_8192 224 240 256
  (interval_append badTest_8192 224 232 240
  badTest_8192_block_28
  badTest_8192_block_29)
  (interval_append badTest_8192 240 248 256
  badTest_8192_block_30
  badTest_8192_block_31)))))
cert_badTestInterval 8192 8448
end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad033 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 8448
cert_badTest_block 8448 0 0 8 8
cert_badTest_block 8448 1 8 16 8
cert_badTest_block 8448 2 16 24 8
cert_badTest_block 8448 3 24 32 8
cert_badTest_block 8448 4 32 40 8
cert_badTest_block 8448 5 40 48 8
cert_badTest_block 8448 6 48 56 8
cert_badTest_block 8448 7 56 64 8
cert_badTest_block 8448 8 64 72 8
cert_badTest_block 8448 9 72 80 8
cert_badTest_block 8448 10 80 88 8
cert_badTest_block 8448 11 88 96 8
cert_badTest_block 8448 12 96 104 8
cert_badTest_block 8448 13 104 112 8
cert_badTest_block 8448 14 112 120 8
cert_badTest_block 8448 15 120 128 8
cert_badTest_block 8448 16 128 136 8
cert_badTest_block 8448 17 136 144 8
cert_badTest_block 8448 18 144 152 8
cert_badTest_block 8448 19 152 160 8
cert_badTest_block 8448 20 160 168 8
cert_badTest_block 8448 21 168 176 8
cert_badTest_block 8448 22 176 184 8
cert_badTest_block 8448 23 184 192 8
cert_badTest_block 8448 24 192 200 8
cert_badTest_block 8448 25 200 208 8
cert_badTest_block 8448 26 208 216 8
cert_badTest_block 8448 27 216 224 8
cert_badTest_block 8448 28 224 232 8
cert_badTest_block 8448 29 232 240 8
cert_badTest_block 8448 30 240 248 8
cert_badTest_block 8448 31 248 256 8
theorem badTest_8448_complete : Interval badTest_8448 0 256 :=
  (interval_append badTest_8448 0 128 256
  (interval_append badTest_8448 0 64 128
  (interval_append badTest_8448 0 32 64
  (interval_append badTest_8448 0 16 32
  (interval_append badTest_8448 0 8 16
  badTest_8448_block_0
  badTest_8448_block_1)
  (interval_append badTest_8448 16 24 32
  badTest_8448_block_2
  badTest_8448_block_3))
  (interval_append badTest_8448 32 48 64
  (interval_append badTest_8448 32 40 48
  badTest_8448_block_4
  badTest_8448_block_5)
  (interval_append badTest_8448 48 56 64
  badTest_8448_block_6
  badTest_8448_block_7)))
  (interval_append badTest_8448 64 96 128
  (interval_append badTest_8448 64 80 96
  (interval_append badTest_8448 64 72 80
  badTest_8448_block_8
  badTest_8448_block_9)
  (interval_append badTest_8448 80 88 96
  badTest_8448_block_10
  badTest_8448_block_11))
  (interval_append badTest_8448 96 112 128
  (interval_append badTest_8448 96 104 112
  badTest_8448_block_12
  badTest_8448_block_13)
  (interval_append badTest_8448 112 120 128
  badTest_8448_block_14
  badTest_8448_block_15))))
  (interval_append badTest_8448 128 192 256
  (interval_append badTest_8448 128 160 192
  (interval_append badTest_8448 128 144 160
  (interval_append badTest_8448 128 136 144
  badTest_8448_block_16
  badTest_8448_block_17)
  (interval_append badTest_8448 144 152 160
  badTest_8448_block_18
  badTest_8448_block_19))
  (interval_append badTest_8448 160 176 192
  (interval_append badTest_8448 160 168 176
  badTest_8448_block_20
  badTest_8448_block_21)
  (interval_append badTest_8448 176 184 192
  badTest_8448_block_22
  badTest_8448_block_23)))
  (interval_append badTest_8448 192 224 256
  (interval_append badTest_8448 192 208 224
  (interval_append badTest_8448 192 200 208
  badTest_8448_block_24
  badTest_8448_block_25)
  (interval_append badTest_8448 208 216 224
  badTest_8448_block_26
  badTest_8448_block_27))
  (interval_append badTest_8448 224 240 256
  (interval_append badTest_8448 224 232 240
  badTest_8448_block_28
  badTest_8448_block_29)
  (interval_append badTest_8448 240 248 256
  badTest_8448_block_30
  badTest_8448_block_31)))))
cert_badTestInterval 8448 8704
end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad034 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 8704
cert_badTest_block 8704 0 0 8 8
cert_badTest_block 8704 1 8 16 8
cert_badTest_block 8704 2 16 24 8
cert_badTest_block 8704 3 24 32 8
cert_badTest_block 8704 4 32 40 8
cert_badTest_block 8704 5 40 48 8
cert_badTest_block 8704 6 48 56 8
cert_badTest_block 8704 7 56 64 8
cert_badTest_block 8704 8 64 72 8
cert_badTest_block 8704 9 72 80 8
cert_badTest_block 8704 10 80 88 8
cert_badTest_block 8704 11 88 96 8
cert_badTest_block 8704 12 96 104 8
cert_badTest_block 8704 13 104 112 8
cert_badTest_block 8704 14 112 120 8
cert_badTest_block 8704 15 120 128 8
cert_badTest_block 8704 16 128 136 8
cert_badTest_block 8704 17 136 144 8
cert_badTest_block 8704 18 144 152 8
cert_badTest_block 8704 19 152 160 8
cert_badTest_block 8704 20 160 168 8
cert_badTest_block 8704 21 168 176 8
cert_badTest_block 8704 22 176 184 8
cert_badTest_block 8704 23 184 192 8
cert_badTest_block 8704 24 192 200 8
cert_badTest_block 8704 25 200 208 8
cert_badTest_block 8704 26 208 216 8
cert_badTest_block 8704 27 216 224 8
cert_badTest_block 8704 28 224 232 8
cert_badTest_block 8704 29 232 240 8
cert_badTest_block 8704 30 240 248 8
cert_badTest_block 8704 31 248 256 8
theorem badTest_8704_complete : Interval badTest_8704 0 256 :=
  (interval_append badTest_8704 0 128 256
  (interval_append badTest_8704 0 64 128
  (interval_append badTest_8704 0 32 64
  (interval_append badTest_8704 0 16 32
  (interval_append badTest_8704 0 8 16
  badTest_8704_block_0
  badTest_8704_block_1)
  (interval_append badTest_8704 16 24 32
  badTest_8704_block_2
  badTest_8704_block_3))
  (interval_append badTest_8704 32 48 64
  (interval_append badTest_8704 32 40 48
  badTest_8704_block_4
  badTest_8704_block_5)
  (interval_append badTest_8704 48 56 64
  badTest_8704_block_6
  badTest_8704_block_7)))
  (interval_append badTest_8704 64 96 128
  (interval_append badTest_8704 64 80 96
  (interval_append badTest_8704 64 72 80
  badTest_8704_block_8
  badTest_8704_block_9)
  (interval_append badTest_8704 80 88 96
  badTest_8704_block_10
  badTest_8704_block_11))
  (interval_append badTest_8704 96 112 128
  (interval_append badTest_8704 96 104 112
  badTest_8704_block_12
  badTest_8704_block_13)
  (interval_append badTest_8704 112 120 128
  badTest_8704_block_14
  badTest_8704_block_15))))
  (interval_append badTest_8704 128 192 256
  (interval_append badTest_8704 128 160 192
  (interval_append badTest_8704 128 144 160
  (interval_append badTest_8704 128 136 144
  badTest_8704_block_16
  badTest_8704_block_17)
  (interval_append badTest_8704 144 152 160
  badTest_8704_block_18
  badTest_8704_block_19))
  (interval_append badTest_8704 160 176 192
  (interval_append badTest_8704 160 168 176
  badTest_8704_block_20
  badTest_8704_block_21)
  (interval_append badTest_8704 176 184 192
  badTest_8704_block_22
  badTest_8704_block_23)))
  (interval_append badTest_8704 192 224 256
  (interval_append badTest_8704 192 208 224
  (interval_append badTest_8704 192 200 208
  badTest_8704_block_24
  badTest_8704_block_25)
  (interval_append badTest_8704 208 216 224
  badTest_8704_block_26
  badTest_8704_block_27))
  (interval_append badTest_8704 224 240 256
  (interval_append badTest_8704 224 232 240
  badTest_8704_block_28
  badTest_8704_block_29)
  (interval_append badTest_8704 240 248 256
  badTest_8704_block_30
  badTest_8704_block_31)))))
cert_badTestInterval 8704 8960
end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
/- RootedSixBase01GrowthCacheBad035 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 8960
cert_badTest_block 8960 0 0 8 8
cert_badTest_block 8960 1 8 16 8
cert_badTest_block 8960 2 16 24 8
cert_badTest_block 8960 3 24 32 8
cert_badTest_block 8960 4 32 40 8
cert_badTest_block 8960 5 40 48 8
cert_badTest_block 8960 6 48 56 8
cert_badTest_block 8960 7 56 64 8
cert_badTest_block 8960 8 64 72 8
cert_badTest_block 8960 9 72 80 8
cert_badTest_block 8960 10 80 88 8
cert_badTest_block 8960 11 88 96 8
cert_badTest_block 8960 12 96 104 8
cert_badTest_block 8960 13 104 112 8
cert_badTest_block 8960 14 112 120 8
cert_badTest_block 8960 15 120 128 8
cert_badTest_block 8960 16 128 136 8
cert_badTest_block 8960 17 136 144 8
cert_badTest_block 8960 18 144 152 8
cert_badTest_block 8960 19 152 160 8
cert_badTest_block 8960 20 160 168 8
cert_badTest_block 8960 21 168 176 8
cert_badTest_block 8960 22 176 184 8
cert_badTest_block 8960 23 184 192 8
cert_badTest_block 8960 24 192 200 8
cert_badTest_block 8960 25 200 208 8
cert_badTest_block 8960 26 208 216 8
cert_badTest_block 8960 27 216 224 8
cert_badTest_block 8960 28 224 232 8
cert_badTest_block 8960 29 232 240 8
cert_badTest_block 8960 30 240 248 8
cert_badTest_block 8960 31 248 256 8
theorem badTest_8960_complete : Interval badTest_8960 0 256 :=
  (interval_append badTest_8960 0 128 256
  (interval_append badTest_8960 0 64 128
  (interval_append badTest_8960 0 32 64
  (interval_append badTest_8960 0 16 32
  (interval_append badTest_8960 0 8 16
  badTest_8960_block_0
  badTest_8960_block_1)
  (interval_append badTest_8960 16 24 32
  badTest_8960_block_2
  badTest_8960_block_3))
  (interval_append badTest_8960 32 48 64
  (interval_append badTest_8960 32 40 48
  badTest_8960_block_4
  badTest_8960_block_5)
  (interval_append badTest_8960 48 56 64
  badTest_8960_block_6
  badTest_8960_block_7)))
  (interval_append badTest_8960 64 96 128
  (interval_append badTest_8960 64 80 96
  (interval_append badTest_8960 64 72 80
  badTest_8960_block_8
  badTest_8960_block_9)
  (interval_append badTest_8960 80 88 96
  badTest_8960_block_10
  badTest_8960_block_11))
  (interval_append badTest_8960 96 112 128
  (interval_append badTest_8960 96 104 112
  badTest_8960_block_12
  badTest_8960_block_13)
  (interval_append badTest_8960 112 120 128
  badTest_8960_block_14
  badTest_8960_block_15))))
  (interval_append badTest_8960 128 192 256
  (interval_append badTest_8960 128 160 192
  (interval_append badTest_8960 128 144 160
  (interval_append badTest_8960 128 136 144
  badTest_8960_block_16
  badTest_8960_block_17)
  (interval_append badTest_8960 144 152 160
  badTest_8960_block_18
  badTest_8960_block_19))
  (interval_append badTest_8960 160 176 192
  (interval_append badTest_8960 160 168 176
  badTest_8960_block_20
  badTest_8960_block_21)
  (interval_append badTest_8960 176 184 192
  badTest_8960_block_22
  badTest_8960_block_23)))
  (interval_append badTest_8960 192 224 256
  (interval_append badTest_8960 192 208 224
  (interval_append badTest_8960 192 200 208
  badTest_8960_block_24
  badTest_8960_block_25)
  (interval_append badTest_8960 208 216 224
  badTest_8960_block_26
  badTest_8960_block_27))
  (interval_append badTest_8960 224 240 256
  (interval_append badTest_8960 224 232 240
  badTest_8960_block_28
  badTest_8960_block_29)
  (interval_append badTest_8960 240 248 256
  badTest_8960_block_30
  badTest_8960_block_31)))))
cert_badTestInterval 8960 9216
end Papers.RationalityTen.RootedCaches.RootedSixBase01

end
end
