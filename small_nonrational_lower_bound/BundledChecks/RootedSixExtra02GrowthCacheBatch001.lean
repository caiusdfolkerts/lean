module
prelude
public meta import LowerSchemas.BundledChecks
public import RootedSixExtra02GrowthCacheData

/- RootedSixExtra02GrowthCacheCells016 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 4096
cert_cellTest_block 4096 0 0 8 8
cert_cellTest_block 4096 1 8 16 8
cert_cellTest_block 4096 2 16 24 8
cert_cellTest_block 4096 3 24 32 8
cert_cellTest_block 4096 4 32 40 8
cert_cellTest_block 4096 5 40 48 8
cert_cellTest_block 4096 6 48 56 8
cert_cellTest_block 4096 7 56 64 8
cert_cellTest_block 4096 8 64 72 8
cert_cellTest_block 4096 9 72 80 8
cert_cellTest_block 4096 10 80 88 8
cert_cellTest_block 4096 11 88 96 8
cert_cellTest_block 4096 12 96 104 8
cert_cellTest_block 4096 13 104 112 8
cert_cellTest_block 4096 14 112 120 8
cert_cellTest_block 4096 15 120 128 8
cert_cellTest_block 4096 16 128 136 8
cert_cellTest_block 4096 17 136 144 8
cert_cellTest_block 4096 18 144 152 8
cert_cellTest_block 4096 19 152 160 8
cert_cellTest_block 4096 20 160 168 8
cert_cellTest_block 4096 21 168 176 8
cert_cellTest_block 4096 22 176 184 8
cert_cellTest_block 4096 23 184 192 8
cert_cellTest_block 4096 24 192 200 8
cert_cellTest_block 4096 25 200 208 8
cert_cellTest_block 4096 26 208 216 8
cert_cellTest_block 4096 27 216 224 8
cert_cellTest_block 4096 28 224 232 8
cert_cellTest_block 4096 29 232 240 8
cert_cellTest_block 4096 30 240 248 8
cert_cellTest_block 4096 31 248 256 8
theorem cellTest_4096_complete : Interval cellTest_4096 0 256 :=
  (interval_append cellTest_4096 0 128 256
  (interval_append cellTest_4096 0 64 128
  (interval_append cellTest_4096 0 32 64
  (interval_append cellTest_4096 0 16 32
  (interval_append cellTest_4096 0 8 16
  cellTest_4096_block_0
  cellTest_4096_block_1)
  (interval_append cellTest_4096 16 24 32
  cellTest_4096_block_2
  cellTest_4096_block_3))
  (interval_append cellTest_4096 32 48 64
  (interval_append cellTest_4096 32 40 48
  cellTest_4096_block_4
  cellTest_4096_block_5)
  (interval_append cellTest_4096 48 56 64
  cellTest_4096_block_6
  cellTest_4096_block_7)))
  (interval_append cellTest_4096 64 96 128
  (interval_append cellTest_4096 64 80 96
  (interval_append cellTest_4096 64 72 80
  cellTest_4096_block_8
  cellTest_4096_block_9)
  (interval_append cellTest_4096 80 88 96
  cellTest_4096_block_10
  cellTest_4096_block_11))
  (interval_append cellTest_4096 96 112 128
  (interval_append cellTest_4096 96 104 112
  cellTest_4096_block_12
  cellTest_4096_block_13)
  (interval_append cellTest_4096 112 120 128
  cellTest_4096_block_14
  cellTest_4096_block_15))))
  (interval_append cellTest_4096 128 192 256
  (interval_append cellTest_4096 128 160 192
  (interval_append cellTest_4096 128 144 160
  (interval_append cellTest_4096 128 136 144
  cellTest_4096_block_16
  cellTest_4096_block_17)
  (interval_append cellTest_4096 144 152 160
  cellTest_4096_block_18
  cellTest_4096_block_19))
  (interval_append cellTest_4096 160 176 192
  (interval_append cellTest_4096 160 168 176
  cellTest_4096_block_20
  cellTest_4096_block_21)
  (interval_append cellTest_4096 176 184 192
  cellTest_4096_block_22
  cellTest_4096_block_23)))
  (interval_append cellTest_4096 192 224 256
  (interval_append cellTest_4096 192 208 224
  (interval_append cellTest_4096 192 200 208
  cellTest_4096_block_24
  cellTest_4096_block_25)
  (interval_append cellTest_4096 208 216 224
  cellTest_4096_block_26
  cellTest_4096_block_27))
  (interval_append cellTest_4096 224 240 256
  (interval_append cellTest_4096 224 232 240
  cellTest_4096_block_28
  cellTest_4096_block_29)
  (interval_append cellTest_4096 240 248 256
  cellTest_4096_block_30
  cellTest_4096_block_31)))))
cert_cellTestInterval 4096 4352
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheCells017 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 4352
cert_cellTest_block 4352 0 0 8 8
cert_cellTest_block 4352 1 8 16 8
cert_cellTest_block 4352 2 16 24 8
cert_cellTest_block 4352 3 24 32 8
cert_cellTest_block 4352 4 32 40 8
cert_cellTest_block 4352 5 40 48 8
cert_cellTest_block 4352 6 48 56 8
cert_cellTest_block 4352 7 56 64 8
cert_cellTest_block 4352 8 64 72 8
cert_cellTest_block 4352 9 72 80 8
cert_cellTest_block 4352 10 80 88 8
cert_cellTest_block 4352 11 88 96 8
cert_cellTest_block 4352 12 96 104 8
cert_cellTest_block 4352 13 104 112 8
cert_cellTest_block 4352 14 112 120 8
cert_cellTest_block 4352 15 120 128 8
cert_cellTest_block 4352 16 128 136 8
cert_cellTest_block 4352 17 136 144 8
cert_cellTest_block 4352 18 144 152 8
cert_cellTest_block 4352 19 152 160 8
cert_cellTest_block 4352 20 160 168 8
cert_cellTest_block 4352 21 168 176 8
cert_cellTest_block 4352 22 176 184 8
cert_cellTest_block 4352 23 184 192 8
cert_cellTest_block 4352 24 192 200 8
cert_cellTest_block 4352 25 200 208 8
cert_cellTest_block 4352 26 208 216 8
cert_cellTest_block 4352 27 216 224 8
cert_cellTest_block 4352 28 224 232 8
cert_cellTest_block 4352 29 232 240 8
cert_cellTest_block 4352 30 240 248 8
cert_cellTest_block 4352 31 248 256 8
theorem cellTest_4352_complete : Interval cellTest_4352 0 256 :=
  (interval_append cellTest_4352 0 128 256
  (interval_append cellTest_4352 0 64 128
  (interval_append cellTest_4352 0 32 64
  (interval_append cellTest_4352 0 16 32
  (interval_append cellTest_4352 0 8 16
  cellTest_4352_block_0
  cellTest_4352_block_1)
  (interval_append cellTest_4352 16 24 32
  cellTest_4352_block_2
  cellTest_4352_block_3))
  (interval_append cellTest_4352 32 48 64
  (interval_append cellTest_4352 32 40 48
  cellTest_4352_block_4
  cellTest_4352_block_5)
  (interval_append cellTest_4352 48 56 64
  cellTest_4352_block_6
  cellTest_4352_block_7)))
  (interval_append cellTest_4352 64 96 128
  (interval_append cellTest_4352 64 80 96
  (interval_append cellTest_4352 64 72 80
  cellTest_4352_block_8
  cellTest_4352_block_9)
  (interval_append cellTest_4352 80 88 96
  cellTest_4352_block_10
  cellTest_4352_block_11))
  (interval_append cellTest_4352 96 112 128
  (interval_append cellTest_4352 96 104 112
  cellTest_4352_block_12
  cellTest_4352_block_13)
  (interval_append cellTest_4352 112 120 128
  cellTest_4352_block_14
  cellTest_4352_block_15))))
  (interval_append cellTest_4352 128 192 256
  (interval_append cellTest_4352 128 160 192
  (interval_append cellTest_4352 128 144 160
  (interval_append cellTest_4352 128 136 144
  cellTest_4352_block_16
  cellTest_4352_block_17)
  (interval_append cellTest_4352 144 152 160
  cellTest_4352_block_18
  cellTest_4352_block_19))
  (interval_append cellTest_4352 160 176 192
  (interval_append cellTest_4352 160 168 176
  cellTest_4352_block_20
  cellTest_4352_block_21)
  (interval_append cellTest_4352 176 184 192
  cellTest_4352_block_22
  cellTest_4352_block_23)))
  (interval_append cellTest_4352 192 224 256
  (interval_append cellTest_4352 192 208 224
  (interval_append cellTest_4352 192 200 208
  cellTest_4352_block_24
  cellTest_4352_block_25)
  (interval_append cellTest_4352 208 216 224
  cellTest_4352_block_26
  cellTest_4352_block_27))
  (interval_append cellTest_4352 224 240 256
  (interval_append cellTest_4352 224 232 240
  cellTest_4352_block_28
  cellTest_4352_block_29)
  (interval_append cellTest_4352 240 248 256
  cellTest_4352_block_30
  cellTest_4352_block_31)))))
cert_cellTestInterval 4352 4608
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheCells018 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 4608
cert_cellTest_block 4608 0 0 8 8
cert_cellTest_block 4608 1 8 16 8
cert_cellTest_block 4608 2 16 24 8
cert_cellTest_block 4608 3 24 32 8
cert_cellTest_block 4608 4 32 40 8
cert_cellTest_block 4608 5 40 48 8
cert_cellTest_block 4608 6 48 56 8
cert_cellTest_block 4608 7 56 64 8
cert_cellTest_block 4608 8 64 72 8
cert_cellTest_block 4608 9 72 80 8
cert_cellTest_block 4608 10 80 88 8
cert_cellTest_block 4608 11 88 96 8
cert_cellTest_block 4608 12 96 104 8
cert_cellTest_block 4608 13 104 112 8
cert_cellTest_block 4608 14 112 120 8
cert_cellTest_block 4608 15 120 128 8
cert_cellTest_block 4608 16 128 136 8
cert_cellTest_block 4608 17 136 144 8
cert_cellTest_block 4608 18 144 152 8
cert_cellTest_block 4608 19 152 160 8
cert_cellTest_block 4608 20 160 168 8
cert_cellTest_block 4608 21 168 176 8
cert_cellTest_block 4608 22 176 184 8
cert_cellTest_block 4608 23 184 192 8
cert_cellTest_block 4608 24 192 200 8
cert_cellTest_block 4608 25 200 208 8
cert_cellTest_block 4608 26 208 216 8
cert_cellTest_block 4608 27 216 224 8
cert_cellTest_block 4608 28 224 232 8
cert_cellTest_block 4608 29 232 240 8
cert_cellTest_block 4608 30 240 248 8
cert_cellTest_block 4608 31 248 256 8
theorem cellTest_4608_complete : Interval cellTest_4608 0 256 :=
  (interval_append cellTest_4608 0 128 256
  (interval_append cellTest_4608 0 64 128
  (interval_append cellTest_4608 0 32 64
  (interval_append cellTest_4608 0 16 32
  (interval_append cellTest_4608 0 8 16
  cellTest_4608_block_0
  cellTest_4608_block_1)
  (interval_append cellTest_4608 16 24 32
  cellTest_4608_block_2
  cellTest_4608_block_3))
  (interval_append cellTest_4608 32 48 64
  (interval_append cellTest_4608 32 40 48
  cellTest_4608_block_4
  cellTest_4608_block_5)
  (interval_append cellTest_4608 48 56 64
  cellTest_4608_block_6
  cellTest_4608_block_7)))
  (interval_append cellTest_4608 64 96 128
  (interval_append cellTest_4608 64 80 96
  (interval_append cellTest_4608 64 72 80
  cellTest_4608_block_8
  cellTest_4608_block_9)
  (interval_append cellTest_4608 80 88 96
  cellTest_4608_block_10
  cellTest_4608_block_11))
  (interval_append cellTest_4608 96 112 128
  (interval_append cellTest_4608 96 104 112
  cellTest_4608_block_12
  cellTest_4608_block_13)
  (interval_append cellTest_4608 112 120 128
  cellTest_4608_block_14
  cellTest_4608_block_15))))
  (interval_append cellTest_4608 128 192 256
  (interval_append cellTest_4608 128 160 192
  (interval_append cellTest_4608 128 144 160
  (interval_append cellTest_4608 128 136 144
  cellTest_4608_block_16
  cellTest_4608_block_17)
  (interval_append cellTest_4608 144 152 160
  cellTest_4608_block_18
  cellTest_4608_block_19))
  (interval_append cellTest_4608 160 176 192
  (interval_append cellTest_4608 160 168 176
  cellTest_4608_block_20
  cellTest_4608_block_21)
  (interval_append cellTest_4608 176 184 192
  cellTest_4608_block_22
  cellTest_4608_block_23)))
  (interval_append cellTest_4608 192 224 256
  (interval_append cellTest_4608 192 208 224
  (interval_append cellTest_4608 192 200 208
  cellTest_4608_block_24
  cellTest_4608_block_25)
  (interval_append cellTest_4608 208 216 224
  cellTest_4608_block_26
  cellTest_4608_block_27))
  (interval_append cellTest_4608 224 240 256
  (interval_append cellTest_4608 224 232 240
  cellTest_4608_block_28
  cellTest_4608_block_29)
  (interval_append cellTest_4608 240 248 256
  cellTest_4608_block_30
  cellTest_4608_block_31)))))
cert_cellTestInterval 4608 4864
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheCells019 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 4864
cert_cellTest_block 4864 0 0 8 8
cert_cellTest_block 4864 1 8 16 8
cert_cellTest_block 4864 2 16 24 8
cert_cellTest_block 4864 3 24 32 8
cert_cellTest_block 4864 4 32 40 8
cert_cellTest_block 4864 5 40 48 8
cert_cellTest_block 4864 6 48 56 8
cert_cellTest_block 4864 7 56 64 8
cert_cellTest_block 4864 8 64 72 8
cert_cellTest_block 4864 9 72 80 8
cert_cellTest_block 4864 10 80 88 8
cert_cellTest_block 4864 11 88 96 8
cert_cellTest_block 4864 12 96 104 8
cert_cellTest_block 4864 13 104 112 8
cert_cellTest_block 4864 14 112 120 8
cert_cellTest_block 4864 15 120 128 8
cert_cellTest_block 4864 16 128 136 8
cert_cellTest_block 4864 17 136 144 8
cert_cellTest_block 4864 18 144 152 8
cert_cellTest_block 4864 19 152 160 8
cert_cellTest_block 4864 20 160 168 8
cert_cellTest_block 4864 21 168 176 8
cert_cellTest_block 4864 22 176 184 8
cert_cellTest_block 4864 23 184 192 8
cert_cellTest_block 4864 24 192 200 8
cert_cellTest_block 4864 25 200 208 8
cert_cellTest_block 4864 26 208 216 8
cert_cellTest_block 4864 27 216 224 8
cert_cellTest_block 4864 28 224 232 8
cert_cellTest_block 4864 29 232 240 8
cert_cellTest_block 4864 30 240 248 8
cert_cellTest_block 4864 31 248 256 8
theorem cellTest_4864_complete : Interval cellTest_4864 0 256 :=
  (interval_append cellTest_4864 0 128 256
  (interval_append cellTest_4864 0 64 128
  (interval_append cellTest_4864 0 32 64
  (interval_append cellTest_4864 0 16 32
  (interval_append cellTest_4864 0 8 16
  cellTest_4864_block_0
  cellTest_4864_block_1)
  (interval_append cellTest_4864 16 24 32
  cellTest_4864_block_2
  cellTest_4864_block_3))
  (interval_append cellTest_4864 32 48 64
  (interval_append cellTest_4864 32 40 48
  cellTest_4864_block_4
  cellTest_4864_block_5)
  (interval_append cellTest_4864 48 56 64
  cellTest_4864_block_6
  cellTest_4864_block_7)))
  (interval_append cellTest_4864 64 96 128
  (interval_append cellTest_4864 64 80 96
  (interval_append cellTest_4864 64 72 80
  cellTest_4864_block_8
  cellTest_4864_block_9)
  (interval_append cellTest_4864 80 88 96
  cellTest_4864_block_10
  cellTest_4864_block_11))
  (interval_append cellTest_4864 96 112 128
  (interval_append cellTest_4864 96 104 112
  cellTest_4864_block_12
  cellTest_4864_block_13)
  (interval_append cellTest_4864 112 120 128
  cellTest_4864_block_14
  cellTest_4864_block_15))))
  (interval_append cellTest_4864 128 192 256
  (interval_append cellTest_4864 128 160 192
  (interval_append cellTest_4864 128 144 160
  (interval_append cellTest_4864 128 136 144
  cellTest_4864_block_16
  cellTest_4864_block_17)
  (interval_append cellTest_4864 144 152 160
  cellTest_4864_block_18
  cellTest_4864_block_19))
  (interval_append cellTest_4864 160 176 192
  (interval_append cellTest_4864 160 168 176
  cellTest_4864_block_20
  cellTest_4864_block_21)
  (interval_append cellTest_4864 176 184 192
  cellTest_4864_block_22
  cellTest_4864_block_23)))
  (interval_append cellTest_4864 192 224 256
  (interval_append cellTest_4864 192 208 224
  (interval_append cellTest_4864 192 200 208
  cellTest_4864_block_24
  cellTest_4864_block_25)
  (interval_append cellTest_4864 208 216 224
  cellTest_4864_block_26
  cellTest_4864_block_27))
  (interval_append cellTest_4864 224 240 256
  (interval_append cellTest_4864 224 232 240
  cellTest_4864_block_28
  cellTest_4864_block_29)
  (interval_append cellTest_4864 240 248 256
  cellTest_4864_block_30
  cellTest_4864_block_31)))))
cert_cellTestInterval 4864 5120
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheCells020 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 5120
cert_cellTest_block 5120 0 0 8 8
cert_cellTest_block 5120 1 8 16 8
cert_cellTest_block 5120 2 16 24 8
cert_cellTest_block 5120 3 24 32 8
cert_cellTest_block 5120 4 32 40 8
cert_cellTest_block 5120 5 40 48 8
cert_cellTest_block 5120 6 48 56 8
cert_cellTest_block 5120 7 56 64 8
cert_cellTest_block 5120 8 64 72 8
cert_cellTest_block 5120 9 72 80 8
cert_cellTest_block 5120 10 80 88 8
cert_cellTest_block 5120 11 88 96 8
cert_cellTest_block 5120 12 96 104 8
cert_cellTest_block 5120 13 104 112 8
cert_cellTest_block 5120 14 112 120 8
cert_cellTest_block 5120 15 120 128 8
cert_cellTest_block 5120 16 128 136 8
cert_cellTest_block 5120 17 136 144 8
cert_cellTest_block 5120 18 144 152 8
cert_cellTest_block 5120 19 152 160 8
cert_cellTest_block 5120 20 160 168 8
cert_cellTest_block 5120 21 168 176 8
cert_cellTest_block 5120 22 176 184 8
cert_cellTest_block 5120 23 184 192 8
cert_cellTest_block 5120 24 192 200 8
cert_cellTest_block 5120 25 200 208 8
cert_cellTest_block 5120 26 208 216 8
cert_cellTest_block 5120 27 216 224 8
cert_cellTest_block 5120 28 224 232 8
cert_cellTest_block 5120 29 232 240 8
cert_cellTest_block 5120 30 240 248 8
cert_cellTest_block 5120 31 248 256 8
theorem cellTest_5120_complete : Interval cellTest_5120 0 256 :=
  (interval_append cellTest_5120 0 128 256
  (interval_append cellTest_5120 0 64 128
  (interval_append cellTest_5120 0 32 64
  (interval_append cellTest_5120 0 16 32
  (interval_append cellTest_5120 0 8 16
  cellTest_5120_block_0
  cellTest_5120_block_1)
  (interval_append cellTest_5120 16 24 32
  cellTest_5120_block_2
  cellTest_5120_block_3))
  (interval_append cellTest_5120 32 48 64
  (interval_append cellTest_5120 32 40 48
  cellTest_5120_block_4
  cellTest_5120_block_5)
  (interval_append cellTest_5120 48 56 64
  cellTest_5120_block_6
  cellTest_5120_block_7)))
  (interval_append cellTest_5120 64 96 128
  (interval_append cellTest_5120 64 80 96
  (interval_append cellTest_5120 64 72 80
  cellTest_5120_block_8
  cellTest_5120_block_9)
  (interval_append cellTest_5120 80 88 96
  cellTest_5120_block_10
  cellTest_5120_block_11))
  (interval_append cellTest_5120 96 112 128
  (interval_append cellTest_5120 96 104 112
  cellTest_5120_block_12
  cellTest_5120_block_13)
  (interval_append cellTest_5120 112 120 128
  cellTest_5120_block_14
  cellTest_5120_block_15))))
  (interval_append cellTest_5120 128 192 256
  (interval_append cellTest_5120 128 160 192
  (interval_append cellTest_5120 128 144 160
  (interval_append cellTest_5120 128 136 144
  cellTest_5120_block_16
  cellTest_5120_block_17)
  (interval_append cellTest_5120 144 152 160
  cellTest_5120_block_18
  cellTest_5120_block_19))
  (interval_append cellTest_5120 160 176 192
  (interval_append cellTest_5120 160 168 176
  cellTest_5120_block_20
  cellTest_5120_block_21)
  (interval_append cellTest_5120 176 184 192
  cellTest_5120_block_22
  cellTest_5120_block_23)))
  (interval_append cellTest_5120 192 224 256
  (interval_append cellTest_5120 192 208 224
  (interval_append cellTest_5120 192 200 208
  cellTest_5120_block_24
  cellTest_5120_block_25)
  (interval_append cellTest_5120 208 216 224
  cellTest_5120_block_26
  cellTest_5120_block_27))
  (interval_append cellTest_5120 224 240 256
  (interval_append cellTest_5120 224 232 240
  cellTest_5120_block_28
  cellTest_5120_block_29)
  (interval_append cellTest_5120 240 248 256
  cellTest_5120_block_30
  cellTest_5120_block_31)))))
cert_cellTestInterval 5120 5376
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheCells021 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 5376
cert_cellTest_block 5376 0 0 8 8
cert_cellTest_block 5376 1 8 16 8
cert_cellTest_block 5376 2 16 24 8
cert_cellTest_block 5376 3 24 32 8
cert_cellTest_block 5376 4 32 40 8
cert_cellTest_block 5376 5 40 48 8
cert_cellTest_block 5376 6 48 56 8
cert_cellTest_block 5376 7 56 64 8
cert_cellTest_block 5376 8 64 72 8
cert_cellTest_block 5376 9 72 80 8
cert_cellTest_block 5376 10 80 88 8
cert_cellTest_block 5376 11 88 96 8
cert_cellTest_block 5376 12 96 104 8
cert_cellTest_block 5376 13 104 112 8
cert_cellTest_block 5376 14 112 120 8
cert_cellTest_block 5376 15 120 128 8
cert_cellTest_block 5376 16 128 136 8
cert_cellTest_block 5376 17 136 144 8
cert_cellTest_block 5376 18 144 152 8
cert_cellTest_block 5376 19 152 160 8
cert_cellTest_block 5376 20 160 168 8
cert_cellTest_block 5376 21 168 176 8
cert_cellTest_block 5376 22 176 184 8
cert_cellTest_block 5376 23 184 192 8
cert_cellTest_block 5376 24 192 200 8
cert_cellTest_block 5376 25 200 208 8
cert_cellTest_block 5376 26 208 216 8
cert_cellTest_block 5376 27 216 224 8
cert_cellTest_block 5376 28 224 232 8
cert_cellTest_block 5376 29 232 240 8
cert_cellTest_block 5376 30 240 248 8
cert_cellTest_block 5376 31 248 256 8
theorem cellTest_5376_complete : Interval cellTest_5376 0 256 :=
  (interval_append cellTest_5376 0 128 256
  (interval_append cellTest_5376 0 64 128
  (interval_append cellTest_5376 0 32 64
  (interval_append cellTest_5376 0 16 32
  (interval_append cellTest_5376 0 8 16
  cellTest_5376_block_0
  cellTest_5376_block_1)
  (interval_append cellTest_5376 16 24 32
  cellTest_5376_block_2
  cellTest_5376_block_3))
  (interval_append cellTest_5376 32 48 64
  (interval_append cellTest_5376 32 40 48
  cellTest_5376_block_4
  cellTest_5376_block_5)
  (interval_append cellTest_5376 48 56 64
  cellTest_5376_block_6
  cellTest_5376_block_7)))
  (interval_append cellTest_5376 64 96 128
  (interval_append cellTest_5376 64 80 96
  (interval_append cellTest_5376 64 72 80
  cellTest_5376_block_8
  cellTest_5376_block_9)
  (interval_append cellTest_5376 80 88 96
  cellTest_5376_block_10
  cellTest_5376_block_11))
  (interval_append cellTest_5376 96 112 128
  (interval_append cellTest_5376 96 104 112
  cellTest_5376_block_12
  cellTest_5376_block_13)
  (interval_append cellTest_5376 112 120 128
  cellTest_5376_block_14
  cellTest_5376_block_15))))
  (interval_append cellTest_5376 128 192 256
  (interval_append cellTest_5376 128 160 192
  (interval_append cellTest_5376 128 144 160
  (interval_append cellTest_5376 128 136 144
  cellTest_5376_block_16
  cellTest_5376_block_17)
  (interval_append cellTest_5376 144 152 160
  cellTest_5376_block_18
  cellTest_5376_block_19))
  (interval_append cellTest_5376 160 176 192
  (interval_append cellTest_5376 160 168 176
  cellTest_5376_block_20
  cellTest_5376_block_21)
  (interval_append cellTest_5376 176 184 192
  cellTest_5376_block_22
  cellTest_5376_block_23)))
  (interval_append cellTest_5376 192 224 256
  (interval_append cellTest_5376 192 208 224
  (interval_append cellTest_5376 192 200 208
  cellTest_5376_block_24
  cellTest_5376_block_25)
  (interval_append cellTest_5376 208 216 224
  cellTest_5376_block_26
  cellTest_5376_block_27))
  (interval_append cellTest_5376 224 240 256
  (interval_append cellTest_5376 224 232 240
  cellTest_5376_block_28
  cellTest_5376_block_29)
  (interval_append cellTest_5376 240 248 256
  cellTest_5376_block_30
  cellTest_5376_block_31)))))
cert_cellTestInterval 5376 5632
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheCells022 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 5632
cert_cellTest_block 5632 0 0 8 8
cert_cellTest_block 5632 1 8 16 8
cert_cellTest_block 5632 2 16 24 8
cert_cellTest_block 5632 3 24 32 8
cert_cellTest_block 5632 4 32 40 8
cert_cellTest_block 5632 5 40 48 8
cert_cellTest_block 5632 6 48 56 8
cert_cellTest_block 5632 7 56 64 8
cert_cellTest_block 5632 8 64 72 8
cert_cellTest_block 5632 9 72 80 8
cert_cellTest_block 5632 10 80 88 8
cert_cellTest_block 5632 11 88 96 8
cert_cellTest_block 5632 12 96 104 8
cert_cellTest_block 5632 13 104 112 8
cert_cellTest_block 5632 14 112 120 8
cert_cellTest_block 5632 15 120 128 8
cert_cellTest_block 5632 16 128 136 8
cert_cellTest_block 5632 17 136 144 8
cert_cellTest_block 5632 18 144 152 8
cert_cellTest_block 5632 19 152 160 8
cert_cellTest_block 5632 20 160 168 8
cert_cellTest_block 5632 21 168 176 8
cert_cellTest_block 5632 22 176 184 8
cert_cellTest_block 5632 23 184 192 8
cert_cellTest_block 5632 24 192 200 8
cert_cellTest_block 5632 25 200 208 8
cert_cellTest_block 5632 26 208 216 8
cert_cellTest_block 5632 27 216 224 8
cert_cellTest_block 5632 28 224 232 8
cert_cellTest_block 5632 29 232 240 8
cert_cellTest_block 5632 30 240 248 8
cert_cellTest_block 5632 31 248 256 8
theorem cellTest_5632_complete : Interval cellTest_5632 0 256 :=
  (interval_append cellTest_5632 0 128 256
  (interval_append cellTest_5632 0 64 128
  (interval_append cellTest_5632 0 32 64
  (interval_append cellTest_5632 0 16 32
  (interval_append cellTest_5632 0 8 16
  cellTest_5632_block_0
  cellTest_5632_block_1)
  (interval_append cellTest_5632 16 24 32
  cellTest_5632_block_2
  cellTest_5632_block_3))
  (interval_append cellTest_5632 32 48 64
  (interval_append cellTest_5632 32 40 48
  cellTest_5632_block_4
  cellTest_5632_block_5)
  (interval_append cellTest_5632 48 56 64
  cellTest_5632_block_6
  cellTest_5632_block_7)))
  (interval_append cellTest_5632 64 96 128
  (interval_append cellTest_5632 64 80 96
  (interval_append cellTest_5632 64 72 80
  cellTest_5632_block_8
  cellTest_5632_block_9)
  (interval_append cellTest_5632 80 88 96
  cellTest_5632_block_10
  cellTest_5632_block_11))
  (interval_append cellTest_5632 96 112 128
  (interval_append cellTest_5632 96 104 112
  cellTest_5632_block_12
  cellTest_5632_block_13)
  (interval_append cellTest_5632 112 120 128
  cellTest_5632_block_14
  cellTest_5632_block_15))))
  (interval_append cellTest_5632 128 192 256
  (interval_append cellTest_5632 128 160 192
  (interval_append cellTest_5632 128 144 160
  (interval_append cellTest_5632 128 136 144
  cellTest_5632_block_16
  cellTest_5632_block_17)
  (interval_append cellTest_5632 144 152 160
  cellTest_5632_block_18
  cellTest_5632_block_19))
  (interval_append cellTest_5632 160 176 192
  (interval_append cellTest_5632 160 168 176
  cellTest_5632_block_20
  cellTest_5632_block_21)
  (interval_append cellTest_5632 176 184 192
  cellTest_5632_block_22
  cellTest_5632_block_23)))
  (interval_append cellTest_5632 192 224 256
  (interval_append cellTest_5632 192 208 224
  (interval_append cellTest_5632 192 200 208
  cellTest_5632_block_24
  cellTest_5632_block_25)
  (interval_append cellTest_5632 208 216 224
  cellTest_5632_block_26
  cellTest_5632_block_27))
  (interval_append cellTest_5632 224 240 256
  (interval_append cellTest_5632 224 232 240
  cellTest_5632_block_28
  cellTest_5632_block_29)
  (interval_append cellTest_5632 240 248 256
  cellTest_5632_block_30
  cellTest_5632_block_31)))))
cert_cellTestInterval 5632 5888
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheCells023 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 5888
cert_cellTest_block 5888 0 0 8 8
cert_cellTest_block 5888 1 8 16 8
cert_cellTest_block 5888 2 16 24 8
cert_cellTest_block 5888 3 24 32 8
cert_cellTest_block 5888 4 32 40 8
cert_cellTest_block 5888 5 40 48 8
cert_cellTest_block 5888 6 48 56 8
cert_cellTest_block 5888 7 56 64 8
cert_cellTest_block 5888 8 64 72 8
cert_cellTest_block 5888 9 72 80 8
cert_cellTest_block 5888 10 80 88 8
cert_cellTest_block 5888 11 88 96 8
cert_cellTest_block 5888 12 96 104 8
cert_cellTest_block 5888 13 104 112 8
cert_cellTest_block 5888 14 112 120 8
cert_cellTest_block 5888 15 120 128 8
cert_cellTest_block 5888 16 128 136 8
cert_cellTest_block 5888 17 136 144 8
cert_cellTest_block 5888 18 144 152 8
cert_cellTest_block 5888 19 152 160 8
cert_cellTest_block 5888 20 160 168 8
cert_cellTest_block 5888 21 168 176 8
cert_cellTest_block 5888 22 176 184 8
cert_cellTest_block 5888 23 184 192 8
cert_cellTest_block 5888 24 192 200 8
cert_cellTest_block 5888 25 200 208 8
cert_cellTest_block 5888 26 208 216 8
cert_cellTest_block 5888 27 216 224 8
cert_cellTest_block 5888 28 224 232 8
cert_cellTest_block 5888 29 232 240 8
cert_cellTest_block 5888 30 240 248 8
cert_cellTest_block 5888 31 248 256 8
theorem cellTest_5888_complete : Interval cellTest_5888 0 256 :=
  (interval_append cellTest_5888 0 128 256
  (interval_append cellTest_5888 0 64 128
  (interval_append cellTest_5888 0 32 64
  (interval_append cellTest_5888 0 16 32
  (interval_append cellTest_5888 0 8 16
  cellTest_5888_block_0
  cellTest_5888_block_1)
  (interval_append cellTest_5888 16 24 32
  cellTest_5888_block_2
  cellTest_5888_block_3))
  (interval_append cellTest_5888 32 48 64
  (interval_append cellTest_5888 32 40 48
  cellTest_5888_block_4
  cellTest_5888_block_5)
  (interval_append cellTest_5888 48 56 64
  cellTest_5888_block_6
  cellTest_5888_block_7)))
  (interval_append cellTest_5888 64 96 128
  (interval_append cellTest_5888 64 80 96
  (interval_append cellTest_5888 64 72 80
  cellTest_5888_block_8
  cellTest_5888_block_9)
  (interval_append cellTest_5888 80 88 96
  cellTest_5888_block_10
  cellTest_5888_block_11))
  (interval_append cellTest_5888 96 112 128
  (interval_append cellTest_5888 96 104 112
  cellTest_5888_block_12
  cellTest_5888_block_13)
  (interval_append cellTest_5888 112 120 128
  cellTest_5888_block_14
  cellTest_5888_block_15))))
  (interval_append cellTest_5888 128 192 256
  (interval_append cellTest_5888 128 160 192
  (interval_append cellTest_5888 128 144 160
  (interval_append cellTest_5888 128 136 144
  cellTest_5888_block_16
  cellTest_5888_block_17)
  (interval_append cellTest_5888 144 152 160
  cellTest_5888_block_18
  cellTest_5888_block_19))
  (interval_append cellTest_5888 160 176 192
  (interval_append cellTest_5888 160 168 176
  cellTest_5888_block_20
  cellTest_5888_block_21)
  (interval_append cellTest_5888 176 184 192
  cellTest_5888_block_22
  cellTest_5888_block_23)))
  (interval_append cellTest_5888 192 224 256
  (interval_append cellTest_5888 192 208 224
  (interval_append cellTest_5888 192 200 208
  cellTest_5888_block_24
  cellTest_5888_block_25)
  (interval_append cellTest_5888 208 216 224
  cellTest_5888_block_26
  cellTest_5888_block_27))
  (interval_append cellTest_5888 224 240 256
  (interval_append cellTest_5888 224 232 240
  cellTest_5888_block_28
  cellTest_5888_block_29)
  (interval_append cellTest_5888 240 248 256
  cellTest_5888_block_30
  cellTest_5888_block_31)))))
cert_cellTestInterval 5888 6144
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheCells024 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 6144
cert_cellTest_block 6144 0 0 8 8
cert_cellTest_block 6144 1 8 16 8
cert_cellTest_block 6144 2 16 24 8
cert_cellTest_block 6144 3 24 32 8
cert_cellTest_block 6144 4 32 40 8
cert_cellTest_block 6144 5 40 48 8
cert_cellTest_block 6144 6 48 56 8
cert_cellTest_block 6144 7 56 64 8
cert_cellTest_block 6144 8 64 72 8
cert_cellTest_block 6144 9 72 80 8
cert_cellTest_block 6144 10 80 88 8
cert_cellTest_block 6144 11 88 96 8
cert_cellTest_block 6144 12 96 104 8
cert_cellTest_block 6144 13 104 112 8
cert_cellTest_block 6144 14 112 120 8
cert_cellTest_block 6144 15 120 128 8
cert_cellTest_block 6144 16 128 136 8
cert_cellTest_block 6144 17 136 144 8
cert_cellTest_block 6144 18 144 152 8
cert_cellTest_block 6144 19 152 160 8
cert_cellTest_block 6144 20 160 168 8
cert_cellTest_block 6144 21 168 176 8
cert_cellTest_block 6144 22 176 184 8
cert_cellTest_block 6144 23 184 192 8
cert_cellTest_block 6144 24 192 200 8
cert_cellTest_block 6144 25 200 208 8
cert_cellTest_block 6144 26 208 216 8
cert_cellTest_block 6144 27 216 224 8
cert_cellTest_block 6144 28 224 232 8
cert_cellTest_block 6144 29 232 240 8
cert_cellTest_block 6144 30 240 248 8
cert_cellTest_block 6144 31 248 256 8
theorem cellTest_6144_complete : Interval cellTest_6144 0 256 :=
  (interval_append cellTest_6144 0 128 256
  (interval_append cellTest_6144 0 64 128
  (interval_append cellTest_6144 0 32 64
  (interval_append cellTest_6144 0 16 32
  (interval_append cellTest_6144 0 8 16
  cellTest_6144_block_0
  cellTest_6144_block_1)
  (interval_append cellTest_6144 16 24 32
  cellTest_6144_block_2
  cellTest_6144_block_3))
  (interval_append cellTest_6144 32 48 64
  (interval_append cellTest_6144 32 40 48
  cellTest_6144_block_4
  cellTest_6144_block_5)
  (interval_append cellTest_6144 48 56 64
  cellTest_6144_block_6
  cellTest_6144_block_7)))
  (interval_append cellTest_6144 64 96 128
  (interval_append cellTest_6144 64 80 96
  (interval_append cellTest_6144 64 72 80
  cellTest_6144_block_8
  cellTest_6144_block_9)
  (interval_append cellTest_6144 80 88 96
  cellTest_6144_block_10
  cellTest_6144_block_11))
  (interval_append cellTest_6144 96 112 128
  (interval_append cellTest_6144 96 104 112
  cellTest_6144_block_12
  cellTest_6144_block_13)
  (interval_append cellTest_6144 112 120 128
  cellTest_6144_block_14
  cellTest_6144_block_15))))
  (interval_append cellTest_6144 128 192 256
  (interval_append cellTest_6144 128 160 192
  (interval_append cellTest_6144 128 144 160
  (interval_append cellTest_6144 128 136 144
  cellTest_6144_block_16
  cellTest_6144_block_17)
  (interval_append cellTest_6144 144 152 160
  cellTest_6144_block_18
  cellTest_6144_block_19))
  (interval_append cellTest_6144 160 176 192
  (interval_append cellTest_6144 160 168 176
  cellTest_6144_block_20
  cellTest_6144_block_21)
  (interval_append cellTest_6144 176 184 192
  cellTest_6144_block_22
  cellTest_6144_block_23)))
  (interval_append cellTest_6144 192 224 256
  (interval_append cellTest_6144 192 208 224
  (interval_append cellTest_6144 192 200 208
  cellTest_6144_block_24
  cellTest_6144_block_25)
  (interval_append cellTest_6144 208 216 224
  cellTest_6144_block_26
  cellTest_6144_block_27))
  (interval_append cellTest_6144 224 240 256
  (interval_append cellTest_6144 224 232 240
  cellTest_6144_block_28
  cellTest_6144_block_29)
  (interval_append cellTest_6144 240 248 256
  cellTest_6144_block_30
  cellTest_6144_block_31)))))
cert_cellTestInterval 6144 6400
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheCells025 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 6400
cert_cellTest_block 6400 0 0 8 8
cert_cellTest_block 6400 1 8 16 8
cert_cellTest_block 6400 2 16 24 8
cert_cellTest_block 6400 3 24 32 8
cert_cellTest_block 6400 4 32 40 8
cert_cellTest_block 6400 5 40 48 8
cert_cellTest_block 6400 6 48 56 8
cert_cellTest_block 6400 7 56 64 8
cert_cellTest_block 6400 8 64 72 8
cert_cellTest_block 6400 9 72 80 8
cert_cellTest_block 6400 10 80 88 8
cert_cellTest_block 6400 11 88 96 8
cert_cellTest_block 6400 12 96 104 8
cert_cellTest_block 6400 13 104 112 8
cert_cellTest_block 6400 14 112 120 8
cert_cellTest_block 6400 15 120 128 8
cert_cellTest_block 6400 16 128 136 8
cert_cellTest_block 6400 17 136 144 8
cert_cellTest_block 6400 18 144 152 8
cert_cellTest_block 6400 19 152 160 8
cert_cellTest_block 6400 20 160 168 8
cert_cellTest_block 6400 21 168 176 8
cert_cellTest_block 6400 22 176 184 8
cert_cellTest_block 6400 23 184 192 8
cert_cellTest_block 6400 24 192 200 8
cert_cellTest_block 6400 25 200 208 8
cert_cellTest_block 6400 26 208 216 8
cert_cellTest_block 6400 27 216 220 4
theorem cellTest_6400_complete : Interval cellTest_6400 0 220 :=
  (interval_append cellTest_6400 0 112 220
  (interval_append cellTest_6400 0 56 112
  (interval_append cellTest_6400 0 24 56
  (interval_append cellTest_6400 0 8 24
  cellTest_6400_block_0
  (interval_append cellTest_6400 8 16 24
  cellTest_6400_block_1
  cellTest_6400_block_2))
  (interval_append cellTest_6400 24 40 56
  (interval_append cellTest_6400 24 32 40
  cellTest_6400_block_3
  cellTest_6400_block_4)
  (interval_append cellTest_6400 40 48 56
  cellTest_6400_block_5
  cellTest_6400_block_6)))
  (interval_append cellTest_6400 56 80 112
  (interval_append cellTest_6400 56 64 80
  cellTest_6400_block_7
  (interval_append cellTest_6400 64 72 80
  cellTest_6400_block_8
  cellTest_6400_block_9))
  (interval_append cellTest_6400 80 96 112
  (interval_append cellTest_6400 80 88 96
  cellTest_6400_block_10
  cellTest_6400_block_11)
  (interval_append cellTest_6400 96 104 112
  cellTest_6400_block_12
  cellTest_6400_block_13))))
  (interval_append cellTest_6400 112 168 220
  (interval_append cellTest_6400 112 136 168
  (interval_append cellTest_6400 112 120 136
  cellTest_6400_block_14
  (interval_append cellTest_6400 120 128 136
  cellTest_6400_block_15
  cellTest_6400_block_16))
  (interval_append cellTest_6400 136 152 168
  (interval_append cellTest_6400 136 144 152
  cellTest_6400_block_17
  cellTest_6400_block_18)
  (interval_append cellTest_6400 152 160 168
  cellTest_6400_block_19
  cellTest_6400_block_20)))
  (interval_append cellTest_6400 168 192 220
  (interval_append cellTest_6400 168 176 192
  cellTest_6400_block_21
  (interval_append cellTest_6400 176 184 192
  cellTest_6400_block_22
  cellTest_6400_block_23))
  (interval_append cellTest_6400 192 208 220
  (interval_append cellTest_6400 192 200 208
  cellTest_6400_block_24
  cellTest_6400_block_25)
  (interval_append cellTest_6400 208 216 220
  cellTest_6400_block_26
  cellTest_6400_block_27)))))
cert_cellTestInterval 6400 6620
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 0
cert_badTest_block 0 0 0 8 8
cert_badTest_block 0 1 8 16 8
cert_badTest_block 0 2 16 24 8
cert_badTest_block 0 3 24 32 8
cert_badTest_block 0 4 32 40 8
cert_badTest_block 0 5 40 48 8
cert_badTest_block 0 6 48 56 8
cert_badTest_block 0 7 56 64 8
cert_badTest_block 0 8 64 72 8
cert_badTest_block 0 9 72 80 8
cert_badTest_block 0 10 80 88 8
cert_badTest_block 0 11 88 96 8
cert_badTest_block 0 12 96 104 8
cert_badTest_block 0 13 104 112 8
cert_badTest_block 0 14 112 120 8
cert_badTest_block 0 15 120 128 8
cert_badTest_block 0 16 128 136 8
cert_badTest_block 0 17 136 144 8
cert_badTest_block 0 18 144 152 8
cert_badTest_block 0 19 152 160 8
cert_badTest_block 0 20 160 168 8
cert_badTest_block 0 21 168 176 8
cert_badTest_block 0 22 176 184 8
cert_badTest_block 0 23 184 192 8
cert_badTest_block 0 24 192 200 8
cert_badTest_block 0 25 200 208 8
cert_badTest_block 0 26 208 216 8
cert_badTest_block 0 27 216 224 8
cert_badTest_block 0 28 224 232 8
cert_badTest_block 0 29 232 240 8
cert_badTest_block 0 30 240 248 8
cert_badTest_block 0 31 248 256 8
theorem badTest_0_complete : Interval badTest_0 0 256 :=
  (interval_append badTest_0 0 128 256
  (interval_append badTest_0 0 64 128
  (interval_append badTest_0 0 32 64
  (interval_append badTest_0 0 16 32
  (interval_append badTest_0 0 8 16
  badTest_0_block_0
  badTest_0_block_1)
  (interval_append badTest_0 16 24 32
  badTest_0_block_2
  badTest_0_block_3))
  (interval_append badTest_0 32 48 64
  (interval_append badTest_0 32 40 48
  badTest_0_block_4
  badTest_0_block_5)
  (interval_append badTest_0 48 56 64
  badTest_0_block_6
  badTest_0_block_7)))
  (interval_append badTest_0 64 96 128
  (interval_append badTest_0 64 80 96
  (interval_append badTest_0 64 72 80
  badTest_0_block_8
  badTest_0_block_9)
  (interval_append badTest_0 80 88 96
  badTest_0_block_10
  badTest_0_block_11))
  (interval_append badTest_0 96 112 128
  (interval_append badTest_0 96 104 112
  badTest_0_block_12
  badTest_0_block_13)
  (interval_append badTest_0 112 120 128
  badTest_0_block_14
  badTest_0_block_15))))
  (interval_append badTest_0 128 192 256
  (interval_append badTest_0 128 160 192
  (interval_append badTest_0 128 144 160
  (interval_append badTest_0 128 136 144
  badTest_0_block_16
  badTest_0_block_17)
  (interval_append badTest_0 144 152 160
  badTest_0_block_18
  badTest_0_block_19))
  (interval_append badTest_0 160 176 192
  (interval_append badTest_0 160 168 176
  badTest_0_block_20
  badTest_0_block_21)
  (interval_append badTest_0 176 184 192
  badTest_0_block_22
  badTest_0_block_23)))
  (interval_append badTest_0 192 224 256
  (interval_append badTest_0 192 208 224
  (interval_append badTest_0 192 200 208
  badTest_0_block_24
  badTest_0_block_25)
  (interval_append badTest_0 208 216 224
  badTest_0_block_26
  badTest_0_block_27))
  (interval_append badTest_0 224 240 256
  (interval_append badTest_0 224 232 240
  badTest_0_block_28
  badTest_0_block_29)
  (interval_append badTest_0 240 248 256
  badTest_0_block_30
  badTest_0_block_31)))))
cert_badTestInterval 0 256
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 256
cert_badTest_block 256 0 0 8 8
cert_badTest_block 256 1 8 16 8
cert_badTest_block 256 2 16 24 8
cert_badTest_block 256 3 24 32 8
cert_badTest_block 256 4 32 40 8
cert_badTest_block 256 5 40 48 8
cert_badTest_block 256 6 48 56 8
cert_badTest_block 256 7 56 64 8
cert_badTest_block 256 8 64 72 8
cert_badTest_block 256 9 72 80 8
cert_badTest_block 256 10 80 88 8
cert_badTest_block 256 11 88 96 8
cert_badTest_block 256 12 96 104 8
cert_badTest_block 256 13 104 112 8
cert_badTest_block 256 14 112 120 8
cert_badTest_block 256 15 120 128 8
cert_badTest_block 256 16 128 136 8
cert_badTest_block 256 17 136 144 8
cert_badTest_block 256 18 144 152 8
cert_badTest_block 256 19 152 160 8
cert_badTest_block 256 20 160 168 8
cert_badTest_block 256 21 168 176 8
cert_badTest_block 256 22 176 184 8
cert_badTest_block 256 23 184 192 8
cert_badTest_block 256 24 192 200 8
cert_badTest_block 256 25 200 208 8
cert_badTest_block 256 26 208 216 8
cert_badTest_block 256 27 216 224 8
cert_badTest_block 256 28 224 232 8
cert_badTest_block 256 29 232 240 8
cert_badTest_block 256 30 240 248 8
cert_badTest_block 256 31 248 256 8
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
cert_badTestInterval 256 512
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 512
cert_badTest_block 512 0 0 8 8
cert_badTest_block 512 1 8 16 8
cert_badTest_block 512 2 16 24 8
cert_badTest_block 512 3 24 32 8
cert_badTest_block 512 4 32 40 8
cert_badTest_block 512 5 40 48 8
cert_badTest_block 512 6 48 56 8
cert_badTest_block 512 7 56 64 8
cert_badTest_block 512 8 64 72 8
cert_badTest_block 512 9 72 80 8
cert_badTest_block 512 10 80 88 8
cert_badTest_block 512 11 88 96 8
cert_badTest_block 512 12 96 104 8
cert_badTest_block 512 13 104 112 8
cert_badTest_block 512 14 112 120 8
cert_badTest_block 512 15 120 128 8
cert_badTest_block 512 16 128 136 8
cert_badTest_block 512 17 136 144 8
cert_badTest_block 512 18 144 152 8
cert_badTest_block 512 19 152 160 8
cert_badTest_block 512 20 160 168 8
cert_badTest_block 512 21 168 176 8
cert_badTest_block 512 22 176 184 8
cert_badTest_block 512 23 184 192 8
cert_badTest_block 512 24 192 200 8
cert_badTest_block 512 25 200 208 8
cert_badTest_block 512 26 208 216 8
cert_badTest_block 512 27 216 224 8
cert_badTest_block 512 28 224 232 8
cert_badTest_block 512 29 232 240 8
cert_badTest_block 512 30 240 248 8
cert_badTest_block 512 31 248 256 8
theorem badTest_512_complete : Interval badTest_512 0 256 :=
  (interval_append badTest_512 0 128 256
  (interval_append badTest_512 0 64 128
  (interval_append badTest_512 0 32 64
  (interval_append badTest_512 0 16 32
  (interval_append badTest_512 0 8 16
  badTest_512_block_0
  badTest_512_block_1)
  (interval_append badTest_512 16 24 32
  badTest_512_block_2
  badTest_512_block_3))
  (interval_append badTest_512 32 48 64
  (interval_append badTest_512 32 40 48
  badTest_512_block_4
  badTest_512_block_5)
  (interval_append badTest_512 48 56 64
  badTest_512_block_6
  badTest_512_block_7)))
  (interval_append badTest_512 64 96 128
  (interval_append badTest_512 64 80 96
  (interval_append badTest_512 64 72 80
  badTest_512_block_8
  badTest_512_block_9)
  (interval_append badTest_512 80 88 96
  badTest_512_block_10
  badTest_512_block_11))
  (interval_append badTest_512 96 112 128
  (interval_append badTest_512 96 104 112
  badTest_512_block_12
  badTest_512_block_13)
  (interval_append badTest_512 112 120 128
  badTest_512_block_14
  badTest_512_block_15))))
  (interval_append badTest_512 128 192 256
  (interval_append badTest_512 128 160 192
  (interval_append badTest_512 128 144 160
  (interval_append badTest_512 128 136 144
  badTest_512_block_16
  badTest_512_block_17)
  (interval_append badTest_512 144 152 160
  badTest_512_block_18
  badTest_512_block_19))
  (interval_append badTest_512 160 176 192
  (interval_append badTest_512 160 168 176
  badTest_512_block_20
  badTest_512_block_21)
  (interval_append badTest_512 176 184 192
  badTest_512_block_22
  badTest_512_block_23)))
  (interval_append badTest_512 192 224 256
  (interval_append badTest_512 192 208 224
  (interval_append badTest_512 192 200 208
  badTest_512_block_24
  badTest_512_block_25)
  (interval_append badTest_512 208 216 224
  badTest_512_block_26
  badTest_512_block_27))
  (interval_append badTest_512 224 240 256
  (interval_append badTest_512 224 232 240
  badTest_512_block_28
  badTest_512_block_29)
  (interval_append badTest_512 240 248 256
  badTest_512_block_30
  badTest_512_block_31)))))
cert_badTestInterval 512 768
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad003 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_badTest 768
cert_badTest_block 768 0 0 8 8
cert_badTest_block 768 1 8 16 8
cert_badTest_block 768 2 16 24 8
cert_badTest_block 768 3 24 32 8
cert_badTest_block 768 4 32 40 8
cert_badTest_block 768 5 40 48 8
cert_badTest_block 768 6 48 56 8
cert_badTest_block 768 7 56 64 8
cert_badTest_block 768 8 64 72 8
cert_badTest_block 768 9 72 80 8
cert_badTest_block 768 10 80 88 8
cert_badTest_block 768 11 88 96 8
cert_badTest_block 768 12 96 104 8
cert_badTest_block 768 13 104 112 8
cert_badTest_block 768 14 112 120 8
cert_badTest_block 768 15 120 128 8
cert_badTest_block 768 16 128 136 8
cert_badTest_block 768 17 136 144 8
cert_badTest_block 768 18 144 152 8
cert_badTest_block 768 19 152 160 8
cert_badTest_block 768 20 160 168 8
cert_badTest_block 768 21 168 176 8
cert_badTest_block 768 22 176 184 8
cert_badTest_block 768 23 184 192 8
cert_badTest_block 768 24 192 200 8
cert_badTest_block 768 25 200 208 8
cert_badTest_block 768 26 208 216 8
cert_badTest_block 768 27 216 224 8
cert_badTest_block 768 28 224 232 8
cert_badTest_block 768 29 232 240 8
cert_badTest_block 768 30 240 248 8
cert_badTest_block 768 31 248 256 8
theorem badTest_768_complete : Interval badTest_768 0 256 :=
  (interval_append badTest_768 0 128 256
  (interval_append badTest_768 0 64 128
  (interval_append badTest_768 0 32 64
  (interval_append badTest_768 0 16 32
  (interval_append badTest_768 0 8 16
  badTest_768_block_0
  badTest_768_block_1)
  (interval_append badTest_768 16 24 32
  badTest_768_block_2
  badTest_768_block_3))
  (interval_append badTest_768 32 48 64
  (interval_append badTest_768 32 40 48
  badTest_768_block_4
  badTest_768_block_5)
  (interval_append badTest_768 48 56 64
  badTest_768_block_6
  badTest_768_block_7)))
  (interval_append badTest_768 64 96 128
  (interval_append badTest_768 64 80 96
  (interval_append badTest_768 64 72 80
  badTest_768_block_8
  badTest_768_block_9)
  (interval_append badTest_768 80 88 96
  badTest_768_block_10
  badTest_768_block_11))
  (interval_append badTest_768 96 112 128
  (interval_append badTest_768 96 104 112
  badTest_768_block_12
  badTest_768_block_13)
  (interval_append badTest_768 112 120 128
  badTest_768_block_14
  badTest_768_block_15))))
  (interval_append badTest_768 128 192 256
  (interval_append badTest_768 128 160 192
  (interval_append badTest_768 128 144 160
  (interval_append badTest_768 128 136 144
  badTest_768_block_16
  badTest_768_block_17)
  (interval_append badTest_768 144 152 160
  badTest_768_block_18
  badTest_768_block_19))
  (interval_append badTest_768 160 176 192
  (interval_append badTest_768 160 168 176
  badTest_768_block_20
  badTest_768_block_21)
  (interval_append badTest_768 176 184 192
  badTest_768_block_22
  badTest_768_block_23)))
  (interval_append badTest_768 192 224 256
  (interval_append badTest_768 192 208 224
  (interval_append badTest_768 192 200 208
  badTest_768_block_24
  badTest_768_block_25)
  (interval_append badTest_768 208 216 224
  badTest_768_block_26
  badTest_768_block_27))
  (interval_append badTest_768 224 240 256
  (interval_append badTest_768 224 232 240
  badTest_768_block_28
  badTest_768_block_29)
  (interval_append badTest_768 240 248 256
  badTest_768_block_30
  badTest_768_block_31)))))
cert_badTestInterval 768 1024
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad004 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad005 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
