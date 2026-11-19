module
prelude
public meta import LowerSchemas.BundledChecks
public import RootedSixBase00GrowthCacheData

/- RootedSixBase00GrowthCacheCells080 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 20480
cert_cellTest_block 20480 0 0 8 8
cert_cellTest_block 20480 1 8 16 8
cert_cellTest_block 20480 2 16 24 8
cert_cellTest_block 20480 3 24 32 8
cert_cellTest_block 20480 4 32 40 8
cert_cellTest_block 20480 5 40 48 8
cert_cellTest_block 20480 6 48 56 8
cert_cellTest_block 20480 7 56 64 8
cert_cellTest_block 20480 8 64 72 8
cert_cellTest_block 20480 9 72 80 8
cert_cellTest_block 20480 10 80 88 8
cert_cellTest_block 20480 11 88 96 8
cert_cellTest_block 20480 12 96 104 8
cert_cellTest_block 20480 13 104 112 8
cert_cellTest_block 20480 14 112 120 8
cert_cellTest_block 20480 15 120 128 8
cert_cellTest_block 20480 16 128 136 8
cert_cellTest_block 20480 17 136 144 8
cert_cellTest_block 20480 18 144 152 8
cert_cellTest_block 20480 19 152 160 8
cert_cellTest_block 20480 20 160 168 8
cert_cellTest_block 20480 21 168 176 8
cert_cellTest_block 20480 22 176 184 8
cert_cellTest_block 20480 23 184 192 8
cert_cellTest_block 20480 24 192 200 8
cert_cellTest_block 20480 25 200 208 8
cert_cellTest_block 20480 26 208 216 8
cert_cellTest_block 20480 27 216 224 8
cert_cellTest_block 20480 28 224 232 8
cert_cellTest_block 20480 29 232 240 8
cert_cellTest_block 20480 30 240 248 8
cert_cellTest_block 20480 31 248 256 8
theorem cellTest_20480_complete : Interval cellTest_20480 0 256 :=
  (interval_append cellTest_20480 0 128 256
  (interval_append cellTest_20480 0 64 128
  (interval_append cellTest_20480 0 32 64
  (interval_append cellTest_20480 0 16 32
  (interval_append cellTest_20480 0 8 16
  cellTest_20480_block_0
  cellTest_20480_block_1)
  (interval_append cellTest_20480 16 24 32
  cellTest_20480_block_2
  cellTest_20480_block_3))
  (interval_append cellTest_20480 32 48 64
  (interval_append cellTest_20480 32 40 48
  cellTest_20480_block_4
  cellTest_20480_block_5)
  (interval_append cellTest_20480 48 56 64
  cellTest_20480_block_6
  cellTest_20480_block_7)))
  (interval_append cellTest_20480 64 96 128
  (interval_append cellTest_20480 64 80 96
  (interval_append cellTest_20480 64 72 80
  cellTest_20480_block_8
  cellTest_20480_block_9)
  (interval_append cellTest_20480 80 88 96
  cellTest_20480_block_10
  cellTest_20480_block_11))
  (interval_append cellTest_20480 96 112 128
  (interval_append cellTest_20480 96 104 112
  cellTest_20480_block_12
  cellTest_20480_block_13)
  (interval_append cellTest_20480 112 120 128
  cellTest_20480_block_14
  cellTest_20480_block_15))))
  (interval_append cellTest_20480 128 192 256
  (interval_append cellTest_20480 128 160 192
  (interval_append cellTest_20480 128 144 160
  (interval_append cellTest_20480 128 136 144
  cellTest_20480_block_16
  cellTest_20480_block_17)
  (interval_append cellTest_20480 144 152 160
  cellTest_20480_block_18
  cellTest_20480_block_19))
  (interval_append cellTest_20480 160 176 192
  (interval_append cellTest_20480 160 168 176
  cellTest_20480_block_20
  cellTest_20480_block_21)
  (interval_append cellTest_20480 176 184 192
  cellTest_20480_block_22
  cellTest_20480_block_23)))
  (interval_append cellTest_20480 192 224 256
  (interval_append cellTest_20480 192 208 224
  (interval_append cellTest_20480 192 200 208
  cellTest_20480_block_24
  cellTest_20480_block_25)
  (interval_append cellTest_20480 208 216 224
  cellTest_20480_block_26
  cellTest_20480_block_27))
  (interval_append cellTest_20480 224 240 256
  (interval_append cellTest_20480 224 232 240
  cellTest_20480_block_28
  cellTest_20480_block_29)
  (interval_append cellTest_20480 240 248 256
  cellTest_20480_block_30
  cellTest_20480_block_31)))))
cert_cellTestInterval 20480 20736
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells081 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 20736
cert_cellTest_block 20736 0 0 8 8
cert_cellTest_block 20736 1 8 16 8
cert_cellTest_block 20736 2 16 24 8
cert_cellTest_block 20736 3 24 32 8
cert_cellTest_block 20736 4 32 40 8
cert_cellTest_block 20736 5 40 48 8
cert_cellTest_block 20736 6 48 56 8
cert_cellTest_block 20736 7 56 64 8
cert_cellTest_block 20736 8 64 72 8
cert_cellTest_block 20736 9 72 80 8
cert_cellTest_block 20736 10 80 88 8
cert_cellTest_block 20736 11 88 96 8
cert_cellTest_block 20736 12 96 104 8
cert_cellTest_block 20736 13 104 112 8
cert_cellTest_block 20736 14 112 120 8
cert_cellTest_block 20736 15 120 128 8
cert_cellTest_block 20736 16 128 136 8
cert_cellTest_block 20736 17 136 144 8
cert_cellTest_block 20736 18 144 152 8
cert_cellTest_block 20736 19 152 160 8
cert_cellTest_block 20736 20 160 168 8
cert_cellTest_block 20736 21 168 176 8
cert_cellTest_block 20736 22 176 184 8
cert_cellTest_block 20736 23 184 192 8
cert_cellTest_block 20736 24 192 200 8
cert_cellTest_block 20736 25 200 208 8
cert_cellTest_block 20736 26 208 216 8
cert_cellTest_block 20736 27 216 224 8
cert_cellTest_block 20736 28 224 232 8
cert_cellTest_block 20736 29 232 240 8
cert_cellTest_block 20736 30 240 248 8
cert_cellTest_block 20736 31 248 256 8
theorem cellTest_20736_complete : Interval cellTest_20736 0 256 :=
  (interval_append cellTest_20736 0 128 256
  (interval_append cellTest_20736 0 64 128
  (interval_append cellTest_20736 0 32 64
  (interval_append cellTest_20736 0 16 32
  (interval_append cellTest_20736 0 8 16
  cellTest_20736_block_0
  cellTest_20736_block_1)
  (interval_append cellTest_20736 16 24 32
  cellTest_20736_block_2
  cellTest_20736_block_3))
  (interval_append cellTest_20736 32 48 64
  (interval_append cellTest_20736 32 40 48
  cellTest_20736_block_4
  cellTest_20736_block_5)
  (interval_append cellTest_20736 48 56 64
  cellTest_20736_block_6
  cellTest_20736_block_7)))
  (interval_append cellTest_20736 64 96 128
  (interval_append cellTest_20736 64 80 96
  (interval_append cellTest_20736 64 72 80
  cellTest_20736_block_8
  cellTest_20736_block_9)
  (interval_append cellTest_20736 80 88 96
  cellTest_20736_block_10
  cellTest_20736_block_11))
  (interval_append cellTest_20736 96 112 128
  (interval_append cellTest_20736 96 104 112
  cellTest_20736_block_12
  cellTest_20736_block_13)
  (interval_append cellTest_20736 112 120 128
  cellTest_20736_block_14
  cellTest_20736_block_15))))
  (interval_append cellTest_20736 128 192 256
  (interval_append cellTest_20736 128 160 192
  (interval_append cellTest_20736 128 144 160
  (interval_append cellTest_20736 128 136 144
  cellTest_20736_block_16
  cellTest_20736_block_17)
  (interval_append cellTest_20736 144 152 160
  cellTest_20736_block_18
  cellTest_20736_block_19))
  (interval_append cellTest_20736 160 176 192
  (interval_append cellTest_20736 160 168 176
  cellTest_20736_block_20
  cellTest_20736_block_21)
  (interval_append cellTest_20736 176 184 192
  cellTest_20736_block_22
  cellTest_20736_block_23)))
  (interval_append cellTest_20736 192 224 256
  (interval_append cellTest_20736 192 208 224
  (interval_append cellTest_20736 192 200 208
  cellTest_20736_block_24
  cellTest_20736_block_25)
  (interval_append cellTest_20736 208 216 224
  cellTest_20736_block_26
  cellTest_20736_block_27))
  (interval_append cellTest_20736 224 240 256
  (interval_append cellTest_20736 224 232 240
  cellTest_20736_block_28
  cellTest_20736_block_29)
  (interval_append cellTest_20736 240 248 256
  cellTest_20736_block_30
  cellTest_20736_block_31)))))
cert_cellTestInterval 20736 20992
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells082 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 20992
cert_cellTest_block 20992 0 0 8 8
cert_cellTest_block 20992 1 8 16 8
cert_cellTest_block 20992 2 16 24 8
cert_cellTest_block 20992 3 24 32 8
cert_cellTest_block 20992 4 32 40 8
cert_cellTest_block 20992 5 40 48 8
cert_cellTest_block 20992 6 48 56 8
cert_cellTest_block 20992 7 56 64 8
cert_cellTest_block 20992 8 64 72 8
cert_cellTest_block 20992 9 72 80 8
cert_cellTest_block 20992 10 80 88 8
cert_cellTest_block 20992 11 88 96 8
cert_cellTest_block 20992 12 96 104 8
cert_cellTest_block 20992 13 104 112 8
cert_cellTest_block 20992 14 112 120 8
cert_cellTest_block 20992 15 120 128 8
cert_cellTest_block 20992 16 128 136 8
cert_cellTest_block 20992 17 136 144 8
cert_cellTest_block 20992 18 144 152 8
cert_cellTest_block 20992 19 152 160 8
cert_cellTest_block 20992 20 160 168 8
cert_cellTest_block 20992 21 168 176 8
cert_cellTest_block 20992 22 176 184 8
cert_cellTest_block 20992 23 184 192 8
cert_cellTest_block 20992 24 192 200 8
cert_cellTest_block 20992 25 200 208 8
cert_cellTest_block 20992 26 208 216 8
cert_cellTest_block 20992 27 216 224 8
cert_cellTest_block 20992 28 224 232 8
cert_cellTest_block 20992 29 232 240 8
cert_cellTest_block 20992 30 240 248 8
cert_cellTest_block 20992 31 248 256 8
theorem cellTest_20992_complete : Interval cellTest_20992 0 256 :=
  (interval_append cellTest_20992 0 128 256
  (interval_append cellTest_20992 0 64 128
  (interval_append cellTest_20992 0 32 64
  (interval_append cellTest_20992 0 16 32
  (interval_append cellTest_20992 0 8 16
  cellTest_20992_block_0
  cellTest_20992_block_1)
  (interval_append cellTest_20992 16 24 32
  cellTest_20992_block_2
  cellTest_20992_block_3))
  (interval_append cellTest_20992 32 48 64
  (interval_append cellTest_20992 32 40 48
  cellTest_20992_block_4
  cellTest_20992_block_5)
  (interval_append cellTest_20992 48 56 64
  cellTest_20992_block_6
  cellTest_20992_block_7)))
  (interval_append cellTest_20992 64 96 128
  (interval_append cellTest_20992 64 80 96
  (interval_append cellTest_20992 64 72 80
  cellTest_20992_block_8
  cellTest_20992_block_9)
  (interval_append cellTest_20992 80 88 96
  cellTest_20992_block_10
  cellTest_20992_block_11))
  (interval_append cellTest_20992 96 112 128
  (interval_append cellTest_20992 96 104 112
  cellTest_20992_block_12
  cellTest_20992_block_13)
  (interval_append cellTest_20992 112 120 128
  cellTest_20992_block_14
  cellTest_20992_block_15))))
  (interval_append cellTest_20992 128 192 256
  (interval_append cellTest_20992 128 160 192
  (interval_append cellTest_20992 128 144 160
  (interval_append cellTest_20992 128 136 144
  cellTest_20992_block_16
  cellTest_20992_block_17)
  (interval_append cellTest_20992 144 152 160
  cellTest_20992_block_18
  cellTest_20992_block_19))
  (interval_append cellTest_20992 160 176 192
  (interval_append cellTest_20992 160 168 176
  cellTest_20992_block_20
  cellTest_20992_block_21)
  (interval_append cellTest_20992 176 184 192
  cellTest_20992_block_22
  cellTest_20992_block_23)))
  (interval_append cellTest_20992 192 224 256
  (interval_append cellTest_20992 192 208 224
  (interval_append cellTest_20992 192 200 208
  cellTest_20992_block_24
  cellTest_20992_block_25)
  (interval_append cellTest_20992 208 216 224
  cellTest_20992_block_26
  cellTest_20992_block_27))
  (interval_append cellTest_20992 224 240 256
  (interval_append cellTest_20992 224 232 240
  cellTest_20992_block_28
  cellTest_20992_block_29)
  (interval_append cellTest_20992 240 248 256
  cellTest_20992_block_30
  cellTest_20992_block_31)))))
cert_cellTestInterval 20992 21248
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells083 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 21248
cert_cellTest_block 21248 0 0 8 8
cert_cellTest_block 21248 1 8 16 8
cert_cellTest_block 21248 2 16 24 8
cert_cellTest_block 21248 3 24 32 8
cert_cellTest_block 21248 4 32 40 8
cert_cellTest_block 21248 5 40 48 8
cert_cellTest_block 21248 6 48 56 8
cert_cellTest_block 21248 7 56 64 8
cert_cellTest_block 21248 8 64 72 8
cert_cellTest_block 21248 9 72 80 8
cert_cellTest_block 21248 10 80 88 8
cert_cellTest_block 21248 11 88 96 8
cert_cellTest_block 21248 12 96 104 8
cert_cellTest_block 21248 13 104 112 8
cert_cellTest_block 21248 14 112 120 8
cert_cellTest_block 21248 15 120 128 8
cert_cellTest_block 21248 16 128 136 8
cert_cellTest_block 21248 17 136 144 8
cert_cellTest_block 21248 18 144 152 8
cert_cellTest_block 21248 19 152 160 8
cert_cellTest_block 21248 20 160 168 8
cert_cellTest_block 21248 21 168 176 8
cert_cellTest_block 21248 22 176 184 8
cert_cellTest_block 21248 23 184 192 8
cert_cellTest_block 21248 24 192 200 8
cert_cellTest_block 21248 25 200 208 8
cert_cellTest_block 21248 26 208 216 8
cert_cellTest_block 21248 27 216 224 8
cert_cellTest_block 21248 28 224 232 8
cert_cellTest_block 21248 29 232 240 8
cert_cellTest_block 21248 30 240 248 8
cert_cellTest_block 21248 31 248 256 8
theorem cellTest_21248_complete : Interval cellTest_21248 0 256 :=
  (interval_append cellTest_21248 0 128 256
  (interval_append cellTest_21248 0 64 128
  (interval_append cellTest_21248 0 32 64
  (interval_append cellTest_21248 0 16 32
  (interval_append cellTest_21248 0 8 16
  cellTest_21248_block_0
  cellTest_21248_block_1)
  (interval_append cellTest_21248 16 24 32
  cellTest_21248_block_2
  cellTest_21248_block_3))
  (interval_append cellTest_21248 32 48 64
  (interval_append cellTest_21248 32 40 48
  cellTest_21248_block_4
  cellTest_21248_block_5)
  (interval_append cellTest_21248 48 56 64
  cellTest_21248_block_6
  cellTest_21248_block_7)))
  (interval_append cellTest_21248 64 96 128
  (interval_append cellTest_21248 64 80 96
  (interval_append cellTest_21248 64 72 80
  cellTest_21248_block_8
  cellTest_21248_block_9)
  (interval_append cellTest_21248 80 88 96
  cellTest_21248_block_10
  cellTest_21248_block_11))
  (interval_append cellTest_21248 96 112 128
  (interval_append cellTest_21248 96 104 112
  cellTest_21248_block_12
  cellTest_21248_block_13)
  (interval_append cellTest_21248 112 120 128
  cellTest_21248_block_14
  cellTest_21248_block_15))))
  (interval_append cellTest_21248 128 192 256
  (interval_append cellTest_21248 128 160 192
  (interval_append cellTest_21248 128 144 160
  (interval_append cellTest_21248 128 136 144
  cellTest_21248_block_16
  cellTest_21248_block_17)
  (interval_append cellTest_21248 144 152 160
  cellTest_21248_block_18
  cellTest_21248_block_19))
  (interval_append cellTest_21248 160 176 192
  (interval_append cellTest_21248 160 168 176
  cellTest_21248_block_20
  cellTest_21248_block_21)
  (interval_append cellTest_21248 176 184 192
  cellTest_21248_block_22
  cellTest_21248_block_23)))
  (interval_append cellTest_21248 192 224 256
  (interval_append cellTest_21248 192 208 224
  (interval_append cellTest_21248 192 200 208
  cellTest_21248_block_24
  cellTest_21248_block_25)
  (interval_append cellTest_21248 208 216 224
  cellTest_21248_block_26
  cellTest_21248_block_27))
  (interval_append cellTest_21248 224 240 256
  (interval_append cellTest_21248 224 232 240
  cellTest_21248_block_28
  cellTest_21248_block_29)
  (interval_append cellTest_21248 240 248 256
  cellTest_21248_block_30
  cellTest_21248_block_31)))))
cert_cellTestInterval 21248 21504
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells084 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 21504
cert_cellTest_block 21504 0 0 8 8
cert_cellTest_block 21504 1 8 16 8
cert_cellTest_block 21504 2 16 24 8
cert_cellTest_block 21504 3 24 32 8
cert_cellTest_block 21504 4 32 40 8
cert_cellTest_block 21504 5 40 48 8
cert_cellTest_block 21504 6 48 56 8
cert_cellTest_block 21504 7 56 64 8
cert_cellTest_block 21504 8 64 72 8
cert_cellTest_block 21504 9 72 80 8
cert_cellTest_block 21504 10 80 88 8
cert_cellTest_block 21504 11 88 96 8
cert_cellTest_block 21504 12 96 104 8
cert_cellTest_block 21504 13 104 112 8
cert_cellTest_block 21504 14 112 120 8
cert_cellTest_block 21504 15 120 128 8
cert_cellTest_block 21504 16 128 136 8
cert_cellTest_block 21504 17 136 144 8
cert_cellTest_block 21504 18 144 152 8
cert_cellTest_block 21504 19 152 160 8
cert_cellTest_block 21504 20 160 168 8
cert_cellTest_block 21504 21 168 176 8
cert_cellTest_block 21504 22 176 184 8
cert_cellTest_block 21504 23 184 192 8
cert_cellTest_block 21504 24 192 200 8
cert_cellTest_block 21504 25 200 208 8
cert_cellTest_block 21504 26 208 216 8
cert_cellTest_block 21504 27 216 224 8
cert_cellTest_block 21504 28 224 232 8
cert_cellTest_block 21504 29 232 240 8
cert_cellTest_block 21504 30 240 248 8
cert_cellTest_block 21504 31 248 256 8
theorem cellTest_21504_complete : Interval cellTest_21504 0 256 :=
  (interval_append cellTest_21504 0 128 256
  (interval_append cellTest_21504 0 64 128
  (interval_append cellTest_21504 0 32 64
  (interval_append cellTest_21504 0 16 32
  (interval_append cellTest_21504 0 8 16
  cellTest_21504_block_0
  cellTest_21504_block_1)
  (interval_append cellTest_21504 16 24 32
  cellTest_21504_block_2
  cellTest_21504_block_3))
  (interval_append cellTest_21504 32 48 64
  (interval_append cellTest_21504 32 40 48
  cellTest_21504_block_4
  cellTest_21504_block_5)
  (interval_append cellTest_21504 48 56 64
  cellTest_21504_block_6
  cellTest_21504_block_7)))
  (interval_append cellTest_21504 64 96 128
  (interval_append cellTest_21504 64 80 96
  (interval_append cellTest_21504 64 72 80
  cellTest_21504_block_8
  cellTest_21504_block_9)
  (interval_append cellTest_21504 80 88 96
  cellTest_21504_block_10
  cellTest_21504_block_11))
  (interval_append cellTest_21504 96 112 128
  (interval_append cellTest_21504 96 104 112
  cellTest_21504_block_12
  cellTest_21504_block_13)
  (interval_append cellTest_21504 112 120 128
  cellTest_21504_block_14
  cellTest_21504_block_15))))
  (interval_append cellTest_21504 128 192 256
  (interval_append cellTest_21504 128 160 192
  (interval_append cellTest_21504 128 144 160
  (interval_append cellTest_21504 128 136 144
  cellTest_21504_block_16
  cellTest_21504_block_17)
  (interval_append cellTest_21504 144 152 160
  cellTest_21504_block_18
  cellTest_21504_block_19))
  (interval_append cellTest_21504 160 176 192
  (interval_append cellTest_21504 160 168 176
  cellTest_21504_block_20
  cellTest_21504_block_21)
  (interval_append cellTest_21504 176 184 192
  cellTest_21504_block_22
  cellTest_21504_block_23)))
  (interval_append cellTest_21504 192 224 256
  (interval_append cellTest_21504 192 208 224
  (interval_append cellTest_21504 192 200 208
  cellTest_21504_block_24
  cellTest_21504_block_25)
  (interval_append cellTest_21504 208 216 224
  cellTest_21504_block_26
  cellTest_21504_block_27))
  (interval_append cellTest_21504 224 240 256
  (interval_append cellTest_21504 224 232 240
  cellTest_21504_block_28
  cellTest_21504_block_29)
  (interval_append cellTest_21504 240 248 256
  cellTest_21504_block_30
  cellTest_21504_block_31)))))
cert_cellTestInterval 21504 21760
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheCells085 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 21760
cert_cellTest_block 21760 0 0 8 8
cert_cellTest_block 21760 1 8 16 8
cert_cellTest_block 21760 2 16 24 8
cert_cellTest_block 21760 3 24 32 8
cert_cellTest_block 21760 4 32 40 8
cert_cellTest_block 21760 5 40 48 8
cert_cellTest_block 21760 6 48 56 8
cert_cellTest_block 21760 7 56 64 8
cert_cellTest_block 21760 8 64 72 8
cert_cellTest_block 21760 9 72 80 8
cert_cellTest_block 21760 10 80 88 8
cert_cellTest_block 21760 11 88 96 8
cert_cellTest_block 21760 12 96 104 8
cert_cellTest_block 21760 13 104 112 8
cert_cellTest_block 21760 14 112 120 8
cert_cellTest_block 21760 15 120 128 8
cert_cellTest_block 21760 16 128 136 8
cert_cellTest_block 21760 17 136 144 8
cert_cellTest_block 21760 18 144 152 8
cert_cellTest_block 21760 19 152 160 8
cert_cellTest_block 21760 20 160 168 8
cert_cellTest_block 21760 21 168 176 8
cert_cellTest_block 21760 22 176 184 8
cert_cellTest_block 21760 23 184 192 8
cert_cellTest_block 21760 24 192 200 8
cert_cellTest_block 21760 25 200 208 8
cert_cellTest_block 21760 26 208 216 8
theorem cellTest_21760_complete : Interval cellTest_21760 0 216 :=
  (interval_append cellTest_21760 0 104 216
  (interval_append cellTest_21760 0 48 104
  (interval_append cellTest_21760 0 24 48
  (interval_append cellTest_21760 0 8 24
  cellTest_21760_block_0
  (interval_append cellTest_21760 8 16 24
  cellTest_21760_block_1
  cellTest_21760_block_2))
  (interval_append cellTest_21760 24 32 48
  cellTest_21760_block_3
  (interval_append cellTest_21760 32 40 48
  cellTest_21760_block_4
  cellTest_21760_block_5)))
  (interval_append cellTest_21760 48 72 104
  (interval_append cellTest_21760 48 56 72
  cellTest_21760_block_6
  (interval_append cellTest_21760 56 64 72
  cellTest_21760_block_7
  cellTest_21760_block_8))
  (interval_append cellTest_21760 72 88 104
  (interval_append cellTest_21760 72 80 88
  cellTest_21760_block_9
  cellTest_21760_block_10)
  (interval_append cellTest_21760 88 96 104
  cellTest_21760_block_11
  cellTest_21760_block_12))))
  (interval_append cellTest_21760 104 160 216
  (interval_append cellTest_21760 104 128 160
  (interval_append cellTest_21760 104 112 128
  cellTest_21760_block_13
  (interval_append cellTest_21760 112 120 128
  cellTest_21760_block_14
  cellTest_21760_block_15))
  (interval_append cellTest_21760 128 144 160
  (interval_append cellTest_21760 128 136 144
  cellTest_21760_block_16
  cellTest_21760_block_17)
  (interval_append cellTest_21760 144 152 160
  cellTest_21760_block_18
  cellTest_21760_block_19)))
  (interval_append cellTest_21760 160 184 216
  (interval_append cellTest_21760 160 168 184
  cellTest_21760_block_20
  (interval_append cellTest_21760 168 176 184
  cellTest_21760_block_21
  cellTest_21760_block_22))
  (interval_append cellTest_21760 184 200 216
  (interval_append cellTest_21760 184 192 200
  cellTest_21760_block_23
  cellTest_21760_block_24)
  (interval_append cellTest_21760 200 208 216
  cellTest_21760_block_25
  cellTest_21760_block_26)))))
cert_cellTestInterval 21760 21976
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad003 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad004 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad005 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad006 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad007 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad008 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
/- RootedSixBase00GrowthCacheBad009 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
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
end Papers.RationalityTen.RootedCaches.RootedSixBase00

end
end
