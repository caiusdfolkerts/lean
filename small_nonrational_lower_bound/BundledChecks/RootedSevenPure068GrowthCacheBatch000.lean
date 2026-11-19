module
prelude
public meta import LowerSchemas.BundledChecks
public import RootedSevenPure068GrowthCacheData

/- RootedSevenPure068GrowthCacheCells000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure068
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 0
cert_cellTest_block 0 0 0 8 8
cert_cellTest_block 0 1 8 16 8
cert_cellTest_block 0 2 16 24 8
cert_cellTest_block 0 3 24 32 8
cert_cellTest_block 0 4 32 40 8
cert_cellTest_block 0 5 40 48 8
cert_cellTest_block 0 6 48 56 8
cert_cellTest_block 0 7 56 64 8
cert_cellTest_block 0 8 64 72 8
cert_cellTest_block 0 9 72 80 8
cert_cellTest_block 0 10 80 88 8
cert_cellTest_block 0 11 88 96 8
cert_cellTest_block 0 12 96 104 8
cert_cellTest_block 0 13 104 112 8
cert_cellTest_block 0 14 112 120 8
cert_cellTest_block 0 15 120 128 8
cert_cellTest_block 0 16 128 136 8
cert_cellTest_block 0 17 136 144 8
cert_cellTest_block 0 18 144 152 8
cert_cellTest_block 0 19 152 160 8
cert_cellTest_block 0 20 160 168 8
cert_cellTest_block 0 21 168 176 8
cert_cellTest_block 0 22 176 184 8
cert_cellTest_block 0 23 184 192 8
cert_cellTest_block 0 24 192 200 8
cert_cellTest_block 0 25 200 208 8
cert_cellTest_block 0 26 208 216 8
cert_cellTest_block 0 27 216 224 8
cert_cellTest_block 0 28 224 232 8
cert_cellTest_block 0 29 232 240 8
cert_cellTest_block 0 30 240 248 8
cert_cellTest_block 0 31 248 256 8
theorem cellTest_0_complete : Interval cellTest_0 0 256 :=
  (interval_append cellTest_0 0 128 256
  (interval_append cellTest_0 0 64 128
  (interval_append cellTest_0 0 32 64
  (interval_append cellTest_0 0 16 32
  (interval_append cellTest_0 0 8 16
  cellTest_0_block_0
  cellTest_0_block_1)
  (interval_append cellTest_0 16 24 32
  cellTest_0_block_2
  cellTest_0_block_3))
  (interval_append cellTest_0 32 48 64
  (interval_append cellTest_0 32 40 48
  cellTest_0_block_4
  cellTest_0_block_5)
  (interval_append cellTest_0 48 56 64
  cellTest_0_block_6
  cellTest_0_block_7)))
  (interval_append cellTest_0 64 96 128
  (interval_append cellTest_0 64 80 96
  (interval_append cellTest_0 64 72 80
  cellTest_0_block_8
  cellTest_0_block_9)
  (interval_append cellTest_0 80 88 96
  cellTest_0_block_10
  cellTest_0_block_11))
  (interval_append cellTest_0 96 112 128
  (interval_append cellTest_0 96 104 112
  cellTest_0_block_12
  cellTest_0_block_13)
  (interval_append cellTest_0 112 120 128
  cellTest_0_block_14
  cellTest_0_block_15))))
  (interval_append cellTest_0 128 192 256
  (interval_append cellTest_0 128 160 192
  (interval_append cellTest_0 128 144 160
  (interval_append cellTest_0 128 136 144
  cellTest_0_block_16
  cellTest_0_block_17)
  (interval_append cellTest_0 144 152 160
  cellTest_0_block_18
  cellTest_0_block_19))
  (interval_append cellTest_0 160 176 192
  (interval_append cellTest_0 160 168 176
  cellTest_0_block_20
  cellTest_0_block_21)
  (interval_append cellTest_0 176 184 192
  cellTest_0_block_22
  cellTest_0_block_23)))
  (interval_append cellTest_0 192 224 256
  (interval_append cellTest_0 192 208 224
  (interval_append cellTest_0 192 200 208
  cellTest_0_block_24
  cellTest_0_block_25)
  (interval_append cellTest_0 208 216 224
  cellTest_0_block_26
  cellTest_0_block_27))
  (interval_append cellTest_0 224 240 256
  (interval_append cellTest_0 224 232 240
  cellTest_0_block_28
  cellTest_0_block_29)
  (interval_append cellTest_0 240 248 256
  cellTest_0_block_30
  cellTest_0_block_31)))))
cert_cellTestInterval 0 256
end Papers.RationalityTen.RootedCaches.RootedSevenPure068

end
end
/- RootedSevenPure068GrowthCacheCells001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure068
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 256
cert_cellTest_block 256 0 0 8 8
cert_cellTest_block 256 1 8 16 8
cert_cellTest_block 256 2 16 24 8
cert_cellTest_block 256 3 24 32 8
cert_cellTest_block 256 4 32 40 8
cert_cellTest_block 256 5 40 48 8
cert_cellTest_block 256 6 48 56 8
cert_cellTest_block 256 7 56 64 8
cert_cellTest_block 256 8 64 72 8
cert_cellTest_block 256 9 72 80 8
cert_cellTest_block 256 10 80 88 8
cert_cellTest_block 256 11 88 96 8
cert_cellTest_block 256 12 96 104 8
cert_cellTest_block 256 13 104 112 8
cert_cellTest_block 256 14 112 120 8
cert_cellTest_block 256 15 120 128 8
cert_cellTest_block 256 16 128 136 8
cert_cellTest_block 256 17 136 144 8
cert_cellTest_block 256 18 144 152 8
cert_cellTest_block 256 19 152 160 8
cert_cellTest_block 256 20 160 168 8
cert_cellTest_block 256 21 168 176 8
cert_cellTest_block 256 22 176 184 8
cert_cellTest_block 256 23 184 192 8
cert_cellTest_block 256 24 192 200 8
cert_cellTest_block 256 25 200 205 5
theorem cellTest_256_complete : Interval cellTest_256 0 205 :=
  (interval_append cellTest_256 0 104 205
  (interval_append cellTest_256 0 48 104
  (interval_append cellTest_256 0 24 48
  (interval_append cellTest_256 0 8 24
  cellTest_256_block_0
  (interval_append cellTest_256 8 16 24
  cellTest_256_block_1
  cellTest_256_block_2))
  (interval_append cellTest_256 24 32 48
  cellTest_256_block_3
  (interval_append cellTest_256 32 40 48
  cellTest_256_block_4
  cellTest_256_block_5)))
  (interval_append cellTest_256 48 72 104
  (interval_append cellTest_256 48 56 72
  cellTest_256_block_6
  (interval_append cellTest_256 56 64 72
  cellTest_256_block_7
  cellTest_256_block_8))
  (interval_append cellTest_256 72 88 104
  (interval_append cellTest_256 72 80 88
  cellTest_256_block_9
  cellTest_256_block_10)
  (interval_append cellTest_256 88 96 104
  cellTest_256_block_11
  cellTest_256_block_12))))
  (interval_append cellTest_256 104 152 205
  (interval_append cellTest_256 104 128 152
  (interval_append cellTest_256 104 112 128
  cellTest_256_block_13
  (interval_append cellTest_256 112 120 128
  cellTest_256_block_14
  cellTest_256_block_15))
  (interval_append cellTest_256 128 136 152
  cellTest_256_block_16
  (interval_append cellTest_256 136 144 152
  cellTest_256_block_17
  cellTest_256_block_18)))
  (interval_append cellTest_256 152 176 205
  (interval_append cellTest_256 152 160 176
  cellTest_256_block_19
  (interval_append cellTest_256 160 168 176
  cellTest_256_block_20
  cellTest_256_block_21))
  (interval_append cellTest_256 176 192 205
  (interval_append cellTest_256 176 184 192
  cellTest_256_block_22
  cellTest_256_block_23)
  (interval_append cellTest_256 192 200 205
  cellTest_256_block_24
  cellTest_256_block_25)))))
cert_cellTestInterval 256 461
end Papers.RationalityTen.RootedCaches.RootedSevenPure068

end
end
/- RootedSevenPure068GrowthCacheBad000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure068
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
end Papers.RationalityTen.RootedCaches.RootedSevenPure068

end
end
/- RootedSevenPure068GrowthCacheBad001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure068
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
cert_badTest_block 256 25 200 205 5
theorem badTest_256_complete : Interval badTest_256 0 205 :=
  (interval_append badTest_256 0 104 205
  (interval_append badTest_256 0 48 104
  (interval_append badTest_256 0 24 48
  (interval_append badTest_256 0 8 24
  badTest_256_block_0
  (interval_append badTest_256 8 16 24
  badTest_256_block_1
  badTest_256_block_2))
  (interval_append badTest_256 24 32 48
  badTest_256_block_3
  (interval_append badTest_256 32 40 48
  badTest_256_block_4
  badTest_256_block_5)))
  (interval_append badTest_256 48 72 104
  (interval_append badTest_256 48 56 72
  badTest_256_block_6
  (interval_append badTest_256 56 64 72
  badTest_256_block_7
  badTest_256_block_8))
  (interval_append badTest_256 72 88 104
  (interval_append badTest_256 72 80 88
  badTest_256_block_9
  badTest_256_block_10)
  (interval_append badTest_256 88 96 104
  badTest_256_block_11
  badTest_256_block_12))))
  (interval_append badTest_256 104 152 205
  (interval_append badTest_256 104 128 152
  (interval_append badTest_256 104 112 128
  badTest_256_block_13
  (interval_append badTest_256 112 120 128
  badTest_256_block_14
  badTest_256_block_15))
  (interval_append badTest_256 128 136 152
  badTest_256_block_16
  (interval_append badTest_256 136 144 152
  badTest_256_block_17
  badTest_256_block_18)))
  (interval_append badTest_256 152 176 205
  (interval_append badTest_256 152 160 176
  badTest_256_block_19
  (interval_append badTest_256 160 168 176
  badTest_256_block_20
  badTest_256_block_21))
  (interval_append badTest_256 176 192 205
  (interval_append badTest_256 176 184 192
  badTest_256_block_22
  badTest_256_block_23)
  (interval_append badTest_256 192 200 205
  badTest_256_block_24
  badTest_256_block_25)))))
cert_badTestInterval 256 461
end Papers.RationalityTen.RootedCaches.RootedSevenPure068

end
end
/- RootedSevenPure068GrowthCacheRidges000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure068
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
end Papers.RationalityTen.RootedCaches.RootedSevenPure068

end
end
/- RootedSevenPure068GrowthCacheRidges001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure068
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
end Papers.RationalityTen.RootedCaches.RootedSevenPure068

end
end
/- RootedSevenPure068GrowthCacheRidges002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure068
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
end Papers.RationalityTen.RootedCaches.RootedSevenPure068

end
end
/- RootedSevenPure068GrowthCacheRidges003 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure068
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_ridgeTest 384
cert_ridgeTest_block 384 0 0 8
cert_ridgeTest_block 384 1 8 16
cert_ridgeTest_block 384 2 16 24
cert_ridgeTest_block 384 3 24 32
cert_ridgeTest_block 384 4 32 40
cert_ridgeTest_block 384 5 40 48
cert_ridgeTest_block 384 6 48 56
cert_ridgeTest_block 384 7 56 64
cert_ridgeTest_block 384 8 64 72
cert_ridgeTest_block 384 9 72 80
cert_ridgeTest_block 384 10 80 88
cert_ridgeTest_block 384 11 88 96
cert_ridgeTest_block 384 12 96 104
cert_ridgeTest_block 384 13 104 112
cert_ridgeTest_block 384 14 112 120
cert_ridgeTest_block 384 15 120 128
cert_ridgeTest_complete 384
cert_ridgeTestInterval 384 512
end Papers.RationalityTen.RootedCaches.RootedSevenPure068

end
end
/- RootedSevenPure068GrowthCacheRidges004 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure068
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
end Papers.RationalityTen.RootedCaches.RootedSevenPure068

end
end
/- RootedSevenPure068GrowthCacheRidges005 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure068
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_ridgeTest 640
cert_ridgeTest_block 640 0 0 8
cert_ridgeTest_block 640 1 8 16
cert_ridgeTest_block 640 2 16 24
cert_ridgeTest_block 640 3 24 32
cert_ridgeTest_block 640 4 32 40
cert_ridgeTest_block 640 5 40 48
cert_ridgeTest_block 640 6 48 56
cert_ridgeTest_block 640 7 56 64
cert_ridgeTest_block 640 8 64 72
cert_ridgeTest_block 640 9 72 80
cert_ridgeTest_block 640 10 80 88
cert_ridgeTest_block 640 11 88 96
cert_ridgeTest_block 640 12 96 104
cert_ridgeTest_block 640 13 104 112
cert_ridgeTest_block 640 14 112 120
cert_ridgeTest_block 640 15 120 128
cert_ridgeTest_complete 640
cert_ridgeTestInterval 640 768
end Papers.RationalityTen.RootedCaches.RootedSevenPure068

end
end
/- RootedSevenPure068GrowthCacheRidges006 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure068
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_ridgeTest 768
cert_ridgeTest_block 768 0 0 8
cert_ridgeTest_block 768 1 8 16
cert_ridgeTest_block 768 2 16 24
cert_ridgeTest_block 768 3 24 32
cert_ridgeTest_block 768 4 32 40
cert_ridgeTest_block 768 5 40 48
cert_ridgeTest_block 768 6 48 56
cert_ridgeTest_block 768 7 56 64
cert_ridgeTest_block 768 8 64 72
cert_ridgeTest_block 768 9 72 80
cert_ridgeTest_block 768 10 80 88
cert_ridgeTest_block 768 11 88 96
cert_ridgeTest_block 768 12 96 104
cert_ridgeTest_block 768 13 104 112
cert_ridgeTest_block 768 14 112 120
cert_ridgeTest_block 768 15 120 128
cert_ridgeTest_complete 768
cert_ridgeTestInterval 768 896
end Papers.RationalityTen.RootedCaches.RootedSevenPure068

end
end
/- RootedSevenPure068GrowthCacheRidges007 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure068
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_ridgeTest 896
cert_ridgeTest_block 896 0 0 8
cert_ridgeTest_block 896 1 8 16
cert_ridgeTest_block 896 2 16 24
cert_ridgeTest_block 896 3 24 32
cert_ridgeTest_block 896 4 32 40
cert_ridgeTest_block 896 5 40 48
cert_ridgeTest_block 896 6 48 56
cert_ridgeTest_block 896 7 56 64
cert_ridgeTest_block 896 8 64 72
cert_ridgeTest_block 896 9 72 80
cert_ridgeTest_block 896 10 80 88
cert_ridgeTest_block 896 11 88 96
cert_ridgeTest_block 896 12 96 104
cert_ridgeTest_block 896 13 104 112
cert_ridgeTest_block 896 14 112 120
cert_ridgeTest_block 896 15 120 128
cert_ridgeTest_complete 896
cert_ridgeTestInterval 896 1024
end Papers.RationalityTen.RootedCaches.RootedSevenPure068

end
end
/- RootedSevenPure068GrowthCacheKinds000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure068
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_kindTest
cert_kindTest_block 0 1
cert_kindTest_block 1 2
cert_kindTest_block 2 3
cert_kindTest_block 3 4
cert_kindTest_block 4 5
cert_kindTest_complete
cert_kindTestInterval
end Papers.RationalityTen.RootedCaches.RootedSevenPure068

end
end
/- RootedSevenPure068GrowthCacheWellFormed000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure068
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
end Papers.RationalityTen.RootedCaches.RootedSevenPure068

end
end
/- RootedSevenPure068GrowthCacheWellFormed001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure068
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
cert_wellFormedTest_block 256 12 192 205 13
theorem wellFormedTest_256_complete : Interval wellFormedTest_256 0 205 :=
  (interval_append wellFormedTest_256 0 96 205
  (interval_append wellFormedTest_256 0 48 96
  (interval_append wellFormedTest_256 0 16 48
  wellFormedTest_256_block_0
  (interval_append wellFormedTest_256 16 32 48
  wellFormedTest_256_block_1
  wellFormedTest_256_block_2))
  (interval_append wellFormedTest_256 48 64 96
  wellFormedTest_256_block_3
  (interval_append wellFormedTest_256 64 80 96
  wellFormedTest_256_block_4
  wellFormedTest_256_block_5)))
  (interval_append wellFormedTest_256 96 144 205
  (interval_append wellFormedTest_256 96 112 144
  wellFormedTest_256_block_6
  (interval_append wellFormedTest_256 112 128 144
  wellFormedTest_256_block_7
  wellFormedTest_256_block_8))
  (interval_append wellFormedTest_256 144 176 205
  (interval_append wellFormedTest_256 144 160 176
  wellFormedTest_256_block_9
  wellFormedTest_256_block_10)
  (interval_append wellFormedTest_256 176 192 205
  wellFormedTest_256_block_11
  wellFormedTest_256_block_12))))
cert_wellFormedTestInterval 256 461
end Papers.RationalityTen.RootedCaches.RootedSevenPure068

end
end
