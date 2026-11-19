module
prelude
public meta import LowerSchemas.BundledChecks
public import RootedSixExtra01GrowthCacheData

/- RootedSixExtra01GrowthCacheCells000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
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
cert_cellTest_block 256 25 200 208 8
cert_cellTest_block 256 26 208 216 8
cert_cellTest_block 256 27 216 224 8
cert_cellTest_block 256 28 224 232 8
cert_cellTest_block 256 29 232 240 8
cert_cellTest_block 256 30 240 248 8
cert_cellTest_block 256 31 248 256 8
theorem cellTest_256_complete : Interval cellTest_256 0 256 :=
  (interval_append cellTest_256 0 128 256
  (interval_append cellTest_256 0 64 128
  (interval_append cellTest_256 0 32 64
  (interval_append cellTest_256 0 16 32
  (interval_append cellTest_256 0 8 16
  cellTest_256_block_0
  cellTest_256_block_1)
  (interval_append cellTest_256 16 24 32
  cellTest_256_block_2
  cellTest_256_block_3))
  (interval_append cellTest_256 32 48 64
  (interval_append cellTest_256 32 40 48
  cellTest_256_block_4
  cellTest_256_block_5)
  (interval_append cellTest_256 48 56 64
  cellTest_256_block_6
  cellTest_256_block_7)))
  (interval_append cellTest_256 64 96 128
  (interval_append cellTest_256 64 80 96
  (interval_append cellTest_256 64 72 80
  cellTest_256_block_8
  cellTest_256_block_9)
  (interval_append cellTest_256 80 88 96
  cellTest_256_block_10
  cellTest_256_block_11))
  (interval_append cellTest_256 96 112 128
  (interval_append cellTest_256 96 104 112
  cellTest_256_block_12
  cellTest_256_block_13)
  (interval_append cellTest_256 112 120 128
  cellTest_256_block_14
  cellTest_256_block_15))))
  (interval_append cellTest_256 128 192 256
  (interval_append cellTest_256 128 160 192
  (interval_append cellTest_256 128 144 160
  (interval_append cellTest_256 128 136 144
  cellTest_256_block_16
  cellTest_256_block_17)
  (interval_append cellTest_256 144 152 160
  cellTest_256_block_18
  cellTest_256_block_19))
  (interval_append cellTest_256 160 176 192
  (interval_append cellTest_256 160 168 176
  cellTest_256_block_20
  cellTest_256_block_21)
  (interval_append cellTest_256 176 184 192
  cellTest_256_block_22
  cellTest_256_block_23)))
  (interval_append cellTest_256 192 224 256
  (interval_append cellTest_256 192 208 224
  (interval_append cellTest_256 192 200 208
  cellTest_256_block_24
  cellTest_256_block_25)
  (interval_append cellTest_256 208 216 224
  cellTest_256_block_26
  cellTest_256_block_27))
  (interval_append cellTest_256 224 240 256
  (interval_append cellTest_256 224 232 240
  cellTest_256_block_28
  cellTest_256_block_29)
  (interval_append cellTest_256 240 248 256
  cellTest_256_block_30
  cellTest_256_block_31)))))
cert_cellTestInterval 256 512
end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 512
cert_cellTest_block 512 0 0 8 8
cert_cellTest_block 512 1 8 16 8
cert_cellTest_block 512 2 16 24 8
cert_cellTest_block 512 3 24 32 8
cert_cellTest_block 512 4 32 40 8
cert_cellTest_block 512 5 40 48 8
cert_cellTest_block 512 6 48 56 8
cert_cellTest_block 512 7 56 64 8
cert_cellTest_block 512 8 64 72 8
cert_cellTest_block 512 9 72 80 8
cert_cellTest_block 512 10 80 88 8
cert_cellTest_block 512 11 88 96 8
cert_cellTest_block 512 12 96 104 8
cert_cellTest_block 512 13 104 112 8
cert_cellTest_block 512 14 112 120 8
cert_cellTest_block 512 15 120 128 8
cert_cellTest_block 512 16 128 136 8
cert_cellTest_block 512 17 136 144 8
cert_cellTest_block 512 18 144 152 8
cert_cellTest_block 512 19 152 160 8
cert_cellTest_block 512 20 160 168 8
cert_cellTest_block 512 21 168 176 8
cert_cellTest_block 512 22 176 184 8
cert_cellTest_block 512 23 184 192 8
cert_cellTest_block 512 24 192 200 8
cert_cellTest_block 512 25 200 208 8
cert_cellTest_block 512 26 208 216 8
cert_cellTest_block 512 27 216 224 8
cert_cellTest_block 512 28 224 232 8
cert_cellTest_block 512 29 232 240 8
cert_cellTest_block 512 30 240 248 8
cert_cellTest_block 512 31 248 256 8
theorem cellTest_512_complete : Interval cellTest_512 0 256 :=
  (interval_append cellTest_512 0 128 256
  (interval_append cellTest_512 0 64 128
  (interval_append cellTest_512 0 32 64
  (interval_append cellTest_512 0 16 32
  (interval_append cellTest_512 0 8 16
  cellTest_512_block_0
  cellTest_512_block_1)
  (interval_append cellTest_512 16 24 32
  cellTest_512_block_2
  cellTest_512_block_3))
  (interval_append cellTest_512 32 48 64
  (interval_append cellTest_512 32 40 48
  cellTest_512_block_4
  cellTest_512_block_5)
  (interval_append cellTest_512 48 56 64
  cellTest_512_block_6
  cellTest_512_block_7)))
  (interval_append cellTest_512 64 96 128
  (interval_append cellTest_512 64 80 96
  (interval_append cellTest_512 64 72 80
  cellTest_512_block_8
  cellTest_512_block_9)
  (interval_append cellTest_512 80 88 96
  cellTest_512_block_10
  cellTest_512_block_11))
  (interval_append cellTest_512 96 112 128
  (interval_append cellTest_512 96 104 112
  cellTest_512_block_12
  cellTest_512_block_13)
  (interval_append cellTest_512 112 120 128
  cellTest_512_block_14
  cellTest_512_block_15))))
  (interval_append cellTest_512 128 192 256
  (interval_append cellTest_512 128 160 192
  (interval_append cellTest_512 128 144 160
  (interval_append cellTest_512 128 136 144
  cellTest_512_block_16
  cellTest_512_block_17)
  (interval_append cellTest_512 144 152 160
  cellTest_512_block_18
  cellTest_512_block_19))
  (interval_append cellTest_512 160 176 192
  (interval_append cellTest_512 160 168 176
  cellTest_512_block_20
  cellTest_512_block_21)
  (interval_append cellTest_512 176 184 192
  cellTest_512_block_22
  cellTest_512_block_23)))
  (interval_append cellTest_512 192 224 256
  (interval_append cellTest_512 192 208 224
  (interval_append cellTest_512 192 200 208
  cellTest_512_block_24
  cellTest_512_block_25)
  (interval_append cellTest_512 208 216 224
  cellTest_512_block_26
  cellTest_512_block_27))
  (interval_append cellTest_512 224 240 256
  (interval_append cellTest_512 224 232 240
  cellTest_512_block_28
  cellTest_512_block_29)
  (interval_append cellTest_512 240 248 256
  cellTest_512_block_30
  cellTest_512_block_31)))))
cert_cellTestInterval 512 768
end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells003 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 768
cert_cellTest_block 768 0 0 8 8
cert_cellTest_block 768 1 8 16 8
cert_cellTest_block 768 2 16 24 8
cert_cellTest_block 768 3 24 32 8
cert_cellTest_block 768 4 32 40 8
cert_cellTest_block 768 5 40 48 8
cert_cellTest_block 768 6 48 56 8
cert_cellTest_block 768 7 56 64 8
cert_cellTest_block 768 8 64 72 8
cert_cellTest_block 768 9 72 80 8
cert_cellTest_block 768 10 80 88 8
cert_cellTest_block 768 11 88 96 8
cert_cellTest_block 768 12 96 104 8
cert_cellTest_block 768 13 104 112 8
cert_cellTest_block 768 14 112 120 8
cert_cellTest_block 768 15 120 128 8
cert_cellTest_block 768 16 128 136 8
cert_cellTest_block 768 17 136 144 8
cert_cellTest_block 768 18 144 152 8
cert_cellTest_block 768 19 152 160 8
cert_cellTest_block 768 20 160 168 8
cert_cellTest_block 768 21 168 176 8
cert_cellTest_block 768 22 176 184 8
cert_cellTest_block 768 23 184 192 8
cert_cellTest_block 768 24 192 200 8
cert_cellTest_block 768 25 200 208 8
cert_cellTest_block 768 26 208 216 8
cert_cellTest_block 768 27 216 224 8
cert_cellTest_block 768 28 224 232 8
cert_cellTest_block 768 29 232 240 8
cert_cellTest_block 768 30 240 248 8
cert_cellTest_block 768 31 248 256 8
theorem cellTest_768_complete : Interval cellTest_768 0 256 :=
  (interval_append cellTest_768 0 128 256
  (interval_append cellTest_768 0 64 128
  (interval_append cellTest_768 0 32 64
  (interval_append cellTest_768 0 16 32
  (interval_append cellTest_768 0 8 16
  cellTest_768_block_0
  cellTest_768_block_1)
  (interval_append cellTest_768 16 24 32
  cellTest_768_block_2
  cellTest_768_block_3))
  (interval_append cellTest_768 32 48 64
  (interval_append cellTest_768 32 40 48
  cellTest_768_block_4
  cellTest_768_block_5)
  (interval_append cellTest_768 48 56 64
  cellTest_768_block_6
  cellTest_768_block_7)))
  (interval_append cellTest_768 64 96 128
  (interval_append cellTest_768 64 80 96
  (interval_append cellTest_768 64 72 80
  cellTest_768_block_8
  cellTest_768_block_9)
  (interval_append cellTest_768 80 88 96
  cellTest_768_block_10
  cellTest_768_block_11))
  (interval_append cellTest_768 96 112 128
  (interval_append cellTest_768 96 104 112
  cellTest_768_block_12
  cellTest_768_block_13)
  (interval_append cellTest_768 112 120 128
  cellTest_768_block_14
  cellTest_768_block_15))))
  (interval_append cellTest_768 128 192 256
  (interval_append cellTest_768 128 160 192
  (interval_append cellTest_768 128 144 160
  (interval_append cellTest_768 128 136 144
  cellTest_768_block_16
  cellTest_768_block_17)
  (interval_append cellTest_768 144 152 160
  cellTest_768_block_18
  cellTest_768_block_19))
  (interval_append cellTest_768 160 176 192
  (interval_append cellTest_768 160 168 176
  cellTest_768_block_20
  cellTest_768_block_21)
  (interval_append cellTest_768 176 184 192
  cellTest_768_block_22
  cellTest_768_block_23)))
  (interval_append cellTest_768 192 224 256
  (interval_append cellTest_768 192 208 224
  (interval_append cellTest_768 192 200 208
  cellTest_768_block_24
  cellTest_768_block_25)
  (interval_append cellTest_768 208 216 224
  cellTest_768_block_26
  cellTest_768_block_27))
  (interval_append cellTest_768 224 240 256
  (interval_append cellTest_768 224 232 240
  cellTest_768_block_28
  cellTest_768_block_29)
  (interval_append cellTest_768 240 248 256
  cellTest_768_block_30
  cellTest_768_block_31)))))
cert_cellTestInterval 768 1024
end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells004 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 1024
cert_cellTest_block 1024 0 0 8 8
cert_cellTest_block 1024 1 8 16 8
cert_cellTest_block 1024 2 16 24 8
cert_cellTest_block 1024 3 24 32 8
cert_cellTest_block 1024 4 32 40 8
cert_cellTest_block 1024 5 40 48 8
cert_cellTest_block 1024 6 48 56 8
cert_cellTest_block 1024 7 56 64 8
cert_cellTest_block 1024 8 64 72 8
cert_cellTest_block 1024 9 72 80 8
cert_cellTest_block 1024 10 80 88 8
cert_cellTest_block 1024 11 88 96 8
cert_cellTest_block 1024 12 96 104 8
cert_cellTest_block 1024 13 104 112 8
cert_cellTest_block 1024 14 112 120 8
cert_cellTest_block 1024 15 120 128 8
cert_cellTest_block 1024 16 128 136 8
cert_cellTest_block 1024 17 136 144 8
cert_cellTest_block 1024 18 144 152 8
cert_cellTest_block 1024 19 152 160 8
cert_cellTest_block 1024 20 160 168 8
cert_cellTest_block 1024 21 168 176 8
cert_cellTest_block 1024 22 176 184 8
cert_cellTest_block 1024 23 184 192 8
cert_cellTest_block 1024 24 192 200 8
cert_cellTest_block 1024 25 200 208 8
cert_cellTest_block 1024 26 208 216 8
cert_cellTest_block 1024 27 216 224 8
cert_cellTest_block 1024 28 224 232 8
cert_cellTest_block 1024 29 232 240 8
cert_cellTest_block 1024 30 240 248 8
cert_cellTest_block 1024 31 248 256 8
theorem cellTest_1024_complete : Interval cellTest_1024 0 256 :=
  (interval_append cellTest_1024 0 128 256
  (interval_append cellTest_1024 0 64 128
  (interval_append cellTest_1024 0 32 64
  (interval_append cellTest_1024 0 16 32
  (interval_append cellTest_1024 0 8 16
  cellTest_1024_block_0
  cellTest_1024_block_1)
  (interval_append cellTest_1024 16 24 32
  cellTest_1024_block_2
  cellTest_1024_block_3))
  (interval_append cellTest_1024 32 48 64
  (interval_append cellTest_1024 32 40 48
  cellTest_1024_block_4
  cellTest_1024_block_5)
  (interval_append cellTest_1024 48 56 64
  cellTest_1024_block_6
  cellTest_1024_block_7)))
  (interval_append cellTest_1024 64 96 128
  (interval_append cellTest_1024 64 80 96
  (interval_append cellTest_1024 64 72 80
  cellTest_1024_block_8
  cellTest_1024_block_9)
  (interval_append cellTest_1024 80 88 96
  cellTest_1024_block_10
  cellTest_1024_block_11))
  (interval_append cellTest_1024 96 112 128
  (interval_append cellTest_1024 96 104 112
  cellTest_1024_block_12
  cellTest_1024_block_13)
  (interval_append cellTest_1024 112 120 128
  cellTest_1024_block_14
  cellTest_1024_block_15))))
  (interval_append cellTest_1024 128 192 256
  (interval_append cellTest_1024 128 160 192
  (interval_append cellTest_1024 128 144 160
  (interval_append cellTest_1024 128 136 144
  cellTest_1024_block_16
  cellTest_1024_block_17)
  (interval_append cellTest_1024 144 152 160
  cellTest_1024_block_18
  cellTest_1024_block_19))
  (interval_append cellTest_1024 160 176 192
  (interval_append cellTest_1024 160 168 176
  cellTest_1024_block_20
  cellTest_1024_block_21)
  (interval_append cellTest_1024 176 184 192
  cellTest_1024_block_22
  cellTest_1024_block_23)))
  (interval_append cellTest_1024 192 224 256
  (interval_append cellTest_1024 192 208 224
  (interval_append cellTest_1024 192 200 208
  cellTest_1024_block_24
  cellTest_1024_block_25)
  (interval_append cellTest_1024 208 216 224
  cellTest_1024_block_26
  cellTest_1024_block_27))
  (interval_append cellTest_1024 224 240 256
  (interval_append cellTest_1024 224 232 240
  cellTest_1024_block_28
  cellTest_1024_block_29)
  (interval_append cellTest_1024 240 248 256
  cellTest_1024_block_30
  cellTest_1024_block_31)))))
cert_cellTestInterval 1024 1280
end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells005 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 1280
cert_cellTest_block 1280 0 0 8 8
cert_cellTest_block 1280 1 8 16 8
cert_cellTest_block 1280 2 16 24 8
cert_cellTest_block 1280 3 24 32 8
cert_cellTest_block 1280 4 32 40 8
cert_cellTest_block 1280 5 40 48 8
cert_cellTest_block 1280 6 48 56 8
cert_cellTest_block 1280 7 56 64 8
cert_cellTest_block 1280 8 64 72 8
cert_cellTest_block 1280 9 72 80 8
cert_cellTest_block 1280 10 80 88 8
cert_cellTest_block 1280 11 88 96 8
cert_cellTest_block 1280 12 96 104 8
cert_cellTest_block 1280 13 104 112 8
cert_cellTest_block 1280 14 112 120 8
cert_cellTest_block 1280 15 120 128 8
cert_cellTest_block 1280 16 128 136 8
cert_cellTest_block 1280 17 136 144 8
cert_cellTest_block 1280 18 144 152 8
cert_cellTest_block 1280 19 152 160 8
cert_cellTest_block 1280 20 160 168 8
cert_cellTest_block 1280 21 168 176 8
cert_cellTest_block 1280 22 176 184 8
cert_cellTest_block 1280 23 184 192 8
cert_cellTest_block 1280 24 192 200 8
cert_cellTest_block 1280 25 200 208 8
cert_cellTest_block 1280 26 208 216 8
cert_cellTest_block 1280 27 216 224 8
cert_cellTest_block 1280 28 224 232 8
cert_cellTest_block 1280 29 232 240 8
cert_cellTest_block 1280 30 240 248 8
cert_cellTest_block 1280 31 248 256 8
theorem cellTest_1280_complete : Interval cellTest_1280 0 256 :=
  (interval_append cellTest_1280 0 128 256
  (interval_append cellTest_1280 0 64 128
  (interval_append cellTest_1280 0 32 64
  (interval_append cellTest_1280 0 16 32
  (interval_append cellTest_1280 0 8 16
  cellTest_1280_block_0
  cellTest_1280_block_1)
  (interval_append cellTest_1280 16 24 32
  cellTest_1280_block_2
  cellTest_1280_block_3))
  (interval_append cellTest_1280 32 48 64
  (interval_append cellTest_1280 32 40 48
  cellTest_1280_block_4
  cellTest_1280_block_5)
  (interval_append cellTest_1280 48 56 64
  cellTest_1280_block_6
  cellTest_1280_block_7)))
  (interval_append cellTest_1280 64 96 128
  (interval_append cellTest_1280 64 80 96
  (interval_append cellTest_1280 64 72 80
  cellTest_1280_block_8
  cellTest_1280_block_9)
  (interval_append cellTest_1280 80 88 96
  cellTest_1280_block_10
  cellTest_1280_block_11))
  (interval_append cellTest_1280 96 112 128
  (interval_append cellTest_1280 96 104 112
  cellTest_1280_block_12
  cellTest_1280_block_13)
  (interval_append cellTest_1280 112 120 128
  cellTest_1280_block_14
  cellTest_1280_block_15))))
  (interval_append cellTest_1280 128 192 256
  (interval_append cellTest_1280 128 160 192
  (interval_append cellTest_1280 128 144 160
  (interval_append cellTest_1280 128 136 144
  cellTest_1280_block_16
  cellTest_1280_block_17)
  (interval_append cellTest_1280 144 152 160
  cellTest_1280_block_18
  cellTest_1280_block_19))
  (interval_append cellTest_1280 160 176 192
  (interval_append cellTest_1280 160 168 176
  cellTest_1280_block_20
  cellTest_1280_block_21)
  (interval_append cellTest_1280 176 184 192
  cellTest_1280_block_22
  cellTest_1280_block_23)))
  (interval_append cellTest_1280 192 224 256
  (interval_append cellTest_1280 192 208 224
  (interval_append cellTest_1280 192 200 208
  cellTest_1280_block_24
  cellTest_1280_block_25)
  (interval_append cellTest_1280 208 216 224
  cellTest_1280_block_26
  cellTest_1280_block_27))
  (interval_append cellTest_1280 224 240 256
  (interval_append cellTest_1280 224 232 240
  cellTest_1280_block_28
  cellTest_1280_block_29)
  (interval_append cellTest_1280 240 248 256
  cellTest_1280_block_30
  cellTest_1280_block_31)))))
cert_cellTestInterval 1280 1536
end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells006 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 1536
cert_cellTest_block 1536 0 0 8 8
cert_cellTest_block 1536 1 8 16 8
cert_cellTest_block 1536 2 16 24 8
cert_cellTest_block 1536 3 24 32 8
cert_cellTest_block 1536 4 32 40 8
cert_cellTest_block 1536 5 40 48 8
cert_cellTest_block 1536 6 48 56 8
cert_cellTest_block 1536 7 56 64 8
cert_cellTest_block 1536 8 64 72 8
cert_cellTest_block 1536 9 72 80 8
cert_cellTest_block 1536 10 80 88 8
cert_cellTest_block 1536 11 88 96 8
cert_cellTest_block 1536 12 96 104 8
cert_cellTest_block 1536 13 104 112 8
cert_cellTest_block 1536 14 112 120 8
cert_cellTest_block 1536 15 120 128 8
cert_cellTest_block 1536 16 128 136 8
cert_cellTest_block 1536 17 136 144 8
cert_cellTest_block 1536 18 144 152 8
cert_cellTest_block 1536 19 152 160 8
cert_cellTest_block 1536 20 160 168 8
cert_cellTest_block 1536 21 168 176 8
cert_cellTest_block 1536 22 176 184 8
cert_cellTest_block 1536 23 184 192 8
cert_cellTest_block 1536 24 192 200 8
cert_cellTest_block 1536 25 200 208 8
cert_cellTest_block 1536 26 208 216 8
cert_cellTest_block 1536 27 216 224 8
cert_cellTest_block 1536 28 224 232 8
cert_cellTest_block 1536 29 232 240 8
cert_cellTest_block 1536 30 240 248 8
cert_cellTest_block 1536 31 248 256 8
theorem cellTest_1536_complete : Interval cellTest_1536 0 256 :=
  (interval_append cellTest_1536 0 128 256
  (interval_append cellTest_1536 0 64 128
  (interval_append cellTest_1536 0 32 64
  (interval_append cellTest_1536 0 16 32
  (interval_append cellTest_1536 0 8 16
  cellTest_1536_block_0
  cellTest_1536_block_1)
  (interval_append cellTest_1536 16 24 32
  cellTest_1536_block_2
  cellTest_1536_block_3))
  (interval_append cellTest_1536 32 48 64
  (interval_append cellTest_1536 32 40 48
  cellTest_1536_block_4
  cellTest_1536_block_5)
  (interval_append cellTest_1536 48 56 64
  cellTest_1536_block_6
  cellTest_1536_block_7)))
  (interval_append cellTest_1536 64 96 128
  (interval_append cellTest_1536 64 80 96
  (interval_append cellTest_1536 64 72 80
  cellTest_1536_block_8
  cellTest_1536_block_9)
  (interval_append cellTest_1536 80 88 96
  cellTest_1536_block_10
  cellTest_1536_block_11))
  (interval_append cellTest_1536 96 112 128
  (interval_append cellTest_1536 96 104 112
  cellTest_1536_block_12
  cellTest_1536_block_13)
  (interval_append cellTest_1536 112 120 128
  cellTest_1536_block_14
  cellTest_1536_block_15))))
  (interval_append cellTest_1536 128 192 256
  (interval_append cellTest_1536 128 160 192
  (interval_append cellTest_1536 128 144 160
  (interval_append cellTest_1536 128 136 144
  cellTest_1536_block_16
  cellTest_1536_block_17)
  (interval_append cellTest_1536 144 152 160
  cellTest_1536_block_18
  cellTest_1536_block_19))
  (interval_append cellTest_1536 160 176 192
  (interval_append cellTest_1536 160 168 176
  cellTest_1536_block_20
  cellTest_1536_block_21)
  (interval_append cellTest_1536 176 184 192
  cellTest_1536_block_22
  cellTest_1536_block_23)))
  (interval_append cellTest_1536 192 224 256
  (interval_append cellTest_1536 192 208 224
  (interval_append cellTest_1536 192 200 208
  cellTest_1536_block_24
  cellTest_1536_block_25)
  (interval_append cellTest_1536 208 216 224
  cellTest_1536_block_26
  cellTest_1536_block_27))
  (interval_append cellTest_1536 224 240 256
  (interval_append cellTest_1536 224 232 240
  cellTest_1536_block_28
  cellTest_1536_block_29)
  (interval_append cellTest_1536 240 248 256
  cellTest_1536_block_30
  cellTest_1536_block_31)))))
cert_cellTestInterval 1536 1792
end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells007 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 1792
cert_cellTest_block 1792 0 0 8 8
cert_cellTest_block 1792 1 8 16 8
cert_cellTest_block 1792 2 16 24 8
cert_cellTest_block 1792 3 24 32 8
cert_cellTest_block 1792 4 32 40 8
cert_cellTest_block 1792 5 40 48 8
cert_cellTest_block 1792 6 48 56 8
cert_cellTest_block 1792 7 56 64 8
cert_cellTest_block 1792 8 64 72 8
cert_cellTest_block 1792 9 72 80 8
cert_cellTest_block 1792 10 80 88 8
cert_cellTest_block 1792 11 88 96 8
cert_cellTest_block 1792 12 96 104 8
cert_cellTest_block 1792 13 104 112 8
cert_cellTest_block 1792 14 112 120 8
cert_cellTest_block 1792 15 120 128 8
cert_cellTest_block 1792 16 128 136 8
cert_cellTest_block 1792 17 136 144 8
cert_cellTest_block 1792 18 144 152 8
cert_cellTest_block 1792 19 152 160 8
cert_cellTest_block 1792 20 160 168 8
cert_cellTest_block 1792 21 168 176 8
cert_cellTest_block 1792 22 176 184 8
cert_cellTest_block 1792 23 184 192 8
cert_cellTest_block 1792 24 192 200 8
cert_cellTest_block 1792 25 200 208 8
cert_cellTest_block 1792 26 208 216 8
cert_cellTest_block 1792 27 216 224 8
cert_cellTest_block 1792 28 224 232 8
cert_cellTest_block 1792 29 232 240 8
cert_cellTest_block 1792 30 240 248 8
cert_cellTest_block 1792 31 248 256 8
theorem cellTest_1792_complete : Interval cellTest_1792 0 256 :=
  (interval_append cellTest_1792 0 128 256
  (interval_append cellTest_1792 0 64 128
  (interval_append cellTest_1792 0 32 64
  (interval_append cellTest_1792 0 16 32
  (interval_append cellTest_1792 0 8 16
  cellTest_1792_block_0
  cellTest_1792_block_1)
  (interval_append cellTest_1792 16 24 32
  cellTest_1792_block_2
  cellTest_1792_block_3))
  (interval_append cellTest_1792 32 48 64
  (interval_append cellTest_1792 32 40 48
  cellTest_1792_block_4
  cellTest_1792_block_5)
  (interval_append cellTest_1792 48 56 64
  cellTest_1792_block_6
  cellTest_1792_block_7)))
  (interval_append cellTest_1792 64 96 128
  (interval_append cellTest_1792 64 80 96
  (interval_append cellTest_1792 64 72 80
  cellTest_1792_block_8
  cellTest_1792_block_9)
  (interval_append cellTest_1792 80 88 96
  cellTest_1792_block_10
  cellTest_1792_block_11))
  (interval_append cellTest_1792 96 112 128
  (interval_append cellTest_1792 96 104 112
  cellTest_1792_block_12
  cellTest_1792_block_13)
  (interval_append cellTest_1792 112 120 128
  cellTest_1792_block_14
  cellTest_1792_block_15))))
  (interval_append cellTest_1792 128 192 256
  (interval_append cellTest_1792 128 160 192
  (interval_append cellTest_1792 128 144 160
  (interval_append cellTest_1792 128 136 144
  cellTest_1792_block_16
  cellTest_1792_block_17)
  (interval_append cellTest_1792 144 152 160
  cellTest_1792_block_18
  cellTest_1792_block_19))
  (interval_append cellTest_1792 160 176 192
  (interval_append cellTest_1792 160 168 176
  cellTest_1792_block_20
  cellTest_1792_block_21)
  (interval_append cellTest_1792 176 184 192
  cellTest_1792_block_22
  cellTest_1792_block_23)))
  (interval_append cellTest_1792 192 224 256
  (interval_append cellTest_1792 192 208 224
  (interval_append cellTest_1792 192 200 208
  cellTest_1792_block_24
  cellTest_1792_block_25)
  (interval_append cellTest_1792 208 216 224
  cellTest_1792_block_26
  cellTest_1792_block_27))
  (interval_append cellTest_1792 224 240 256
  (interval_append cellTest_1792 224 232 240
  cellTest_1792_block_28
  cellTest_1792_block_29)
  (interval_append cellTest_1792 240 248 256
  cellTest_1792_block_30
  cellTest_1792_block_31)))))
cert_cellTestInterval 1792 2048
end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells008 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 2048
cert_cellTest_block 2048 0 0 8 8
cert_cellTest_block 2048 1 8 16 8
cert_cellTest_block 2048 2 16 24 8
cert_cellTest_block 2048 3 24 32 8
cert_cellTest_block 2048 4 32 40 8
cert_cellTest_block 2048 5 40 48 8
cert_cellTest_block 2048 6 48 56 8
cert_cellTest_block 2048 7 56 64 8
cert_cellTest_block 2048 8 64 72 8
cert_cellTest_block 2048 9 72 80 8
cert_cellTest_block 2048 10 80 88 8
cert_cellTest_block 2048 11 88 96 8
cert_cellTest_block 2048 12 96 104 8
cert_cellTest_block 2048 13 104 112 8
cert_cellTest_block 2048 14 112 120 8
cert_cellTest_block 2048 15 120 128 8
cert_cellTest_block 2048 16 128 136 8
cert_cellTest_block 2048 17 136 144 8
cert_cellTest_block 2048 18 144 152 8
cert_cellTest_block 2048 19 152 160 8
cert_cellTest_block 2048 20 160 168 8
cert_cellTest_block 2048 21 168 176 8
cert_cellTest_block 2048 22 176 184 8
cert_cellTest_block 2048 23 184 192 8
cert_cellTest_block 2048 24 192 200 8
cert_cellTest_block 2048 25 200 208 8
cert_cellTest_block 2048 26 208 216 8
cert_cellTest_block 2048 27 216 224 8
cert_cellTest_block 2048 28 224 232 8
cert_cellTest_block 2048 29 232 240 8
cert_cellTest_block 2048 30 240 248 8
cert_cellTest_block 2048 31 248 256 8
theorem cellTest_2048_complete : Interval cellTest_2048 0 256 :=
  (interval_append cellTest_2048 0 128 256
  (interval_append cellTest_2048 0 64 128
  (interval_append cellTest_2048 0 32 64
  (interval_append cellTest_2048 0 16 32
  (interval_append cellTest_2048 0 8 16
  cellTest_2048_block_0
  cellTest_2048_block_1)
  (interval_append cellTest_2048 16 24 32
  cellTest_2048_block_2
  cellTest_2048_block_3))
  (interval_append cellTest_2048 32 48 64
  (interval_append cellTest_2048 32 40 48
  cellTest_2048_block_4
  cellTest_2048_block_5)
  (interval_append cellTest_2048 48 56 64
  cellTest_2048_block_6
  cellTest_2048_block_7)))
  (interval_append cellTest_2048 64 96 128
  (interval_append cellTest_2048 64 80 96
  (interval_append cellTest_2048 64 72 80
  cellTest_2048_block_8
  cellTest_2048_block_9)
  (interval_append cellTest_2048 80 88 96
  cellTest_2048_block_10
  cellTest_2048_block_11))
  (interval_append cellTest_2048 96 112 128
  (interval_append cellTest_2048 96 104 112
  cellTest_2048_block_12
  cellTest_2048_block_13)
  (interval_append cellTest_2048 112 120 128
  cellTest_2048_block_14
  cellTest_2048_block_15))))
  (interval_append cellTest_2048 128 192 256
  (interval_append cellTest_2048 128 160 192
  (interval_append cellTest_2048 128 144 160
  (interval_append cellTest_2048 128 136 144
  cellTest_2048_block_16
  cellTest_2048_block_17)
  (interval_append cellTest_2048 144 152 160
  cellTest_2048_block_18
  cellTest_2048_block_19))
  (interval_append cellTest_2048 160 176 192
  (interval_append cellTest_2048 160 168 176
  cellTest_2048_block_20
  cellTest_2048_block_21)
  (interval_append cellTest_2048 176 184 192
  cellTest_2048_block_22
  cellTest_2048_block_23)))
  (interval_append cellTest_2048 192 224 256
  (interval_append cellTest_2048 192 208 224
  (interval_append cellTest_2048 192 200 208
  cellTest_2048_block_24
  cellTest_2048_block_25)
  (interval_append cellTest_2048 208 216 224
  cellTest_2048_block_26
  cellTest_2048_block_27))
  (interval_append cellTest_2048 224 240 256
  (interval_append cellTest_2048 224 232 240
  cellTest_2048_block_28
  cellTest_2048_block_29)
  (interval_append cellTest_2048 240 248 256
  cellTest_2048_block_30
  cellTest_2048_block_31)))))
cert_cellTestInterval 2048 2304
end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells009 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 2304
cert_cellTest_block 2304 0 0 8 8
cert_cellTest_block 2304 1 8 16 8
cert_cellTest_block 2304 2 16 24 8
cert_cellTest_block 2304 3 24 32 8
cert_cellTest_block 2304 4 32 40 8
cert_cellTest_block 2304 5 40 48 8
cert_cellTest_block 2304 6 48 56 8
cert_cellTest_block 2304 7 56 64 8
cert_cellTest_block 2304 8 64 72 8
cert_cellTest_block 2304 9 72 80 8
cert_cellTest_block 2304 10 80 88 8
cert_cellTest_block 2304 11 88 96 8
cert_cellTest_block 2304 12 96 104 8
cert_cellTest_block 2304 13 104 112 8
cert_cellTest_block 2304 14 112 120 8
cert_cellTest_block 2304 15 120 128 8
cert_cellTest_block 2304 16 128 136 8
cert_cellTest_block 2304 17 136 144 8
cert_cellTest_block 2304 18 144 152 8
cert_cellTest_block 2304 19 152 160 8
cert_cellTest_block 2304 20 160 168 8
cert_cellTest_block 2304 21 168 176 8
cert_cellTest_block 2304 22 176 184 8
cert_cellTest_block 2304 23 184 192 8
cert_cellTest_block 2304 24 192 200 8
cert_cellTest_block 2304 25 200 208 8
cert_cellTest_block 2304 26 208 216 8
cert_cellTest_block 2304 27 216 224 8
cert_cellTest_block 2304 28 224 232 8
cert_cellTest_block 2304 29 232 240 8
cert_cellTest_block 2304 30 240 248 8
cert_cellTest_block 2304 31 248 256 8
theorem cellTest_2304_complete : Interval cellTest_2304 0 256 :=
  (interval_append cellTest_2304 0 128 256
  (interval_append cellTest_2304 0 64 128
  (interval_append cellTest_2304 0 32 64
  (interval_append cellTest_2304 0 16 32
  (interval_append cellTest_2304 0 8 16
  cellTest_2304_block_0
  cellTest_2304_block_1)
  (interval_append cellTest_2304 16 24 32
  cellTest_2304_block_2
  cellTest_2304_block_3))
  (interval_append cellTest_2304 32 48 64
  (interval_append cellTest_2304 32 40 48
  cellTest_2304_block_4
  cellTest_2304_block_5)
  (interval_append cellTest_2304 48 56 64
  cellTest_2304_block_6
  cellTest_2304_block_7)))
  (interval_append cellTest_2304 64 96 128
  (interval_append cellTest_2304 64 80 96
  (interval_append cellTest_2304 64 72 80
  cellTest_2304_block_8
  cellTest_2304_block_9)
  (interval_append cellTest_2304 80 88 96
  cellTest_2304_block_10
  cellTest_2304_block_11))
  (interval_append cellTest_2304 96 112 128
  (interval_append cellTest_2304 96 104 112
  cellTest_2304_block_12
  cellTest_2304_block_13)
  (interval_append cellTest_2304 112 120 128
  cellTest_2304_block_14
  cellTest_2304_block_15))))
  (interval_append cellTest_2304 128 192 256
  (interval_append cellTest_2304 128 160 192
  (interval_append cellTest_2304 128 144 160
  (interval_append cellTest_2304 128 136 144
  cellTest_2304_block_16
  cellTest_2304_block_17)
  (interval_append cellTest_2304 144 152 160
  cellTest_2304_block_18
  cellTest_2304_block_19))
  (interval_append cellTest_2304 160 176 192
  (interval_append cellTest_2304 160 168 176
  cellTest_2304_block_20
  cellTest_2304_block_21)
  (interval_append cellTest_2304 176 184 192
  cellTest_2304_block_22
  cellTest_2304_block_23)))
  (interval_append cellTest_2304 192 224 256
  (interval_append cellTest_2304 192 208 224
  (interval_append cellTest_2304 192 200 208
  cellTest_2304_block_24
  cellTest_2304_block_25)
  (interval_append cellTest_2304 208 216 224
  cellTest_2304_block_26
  cellTest_2304_block_27))
  (interval_append cellTest_2304 224 240 256
  (interval_append cellTest_2304 224 232 240
  cellTest_2304_block_28
  cellTest_2304_block_29)
  (interval_append cellTest_2304 240 248 256
  cellTest_2304_block_30
  cellTest_2304_block_31)))))
cert_cellTestInterval 2304 2560
end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells010 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 2560
cert_cellTest_block 2560 0 0 8 8
cert_cellTest_block 2560 1 8 16 8
cert_cellTest_block 2560 2 16 24 8
cert_cellTest_block 2560 3 24 32 8
cert_cellTest_block 2560 4 32 40 8
cert_cellTest_block 2560 5 40 48 8
cert_cellTest_block 2560 6 48 56 8
cert_cellTest_block 2560 7 56 64 8
cert_cellTest_block 2560 8 64 72 8
cert_cellTest_block 2560 9 72 80 8
cert_cellTest_block 2560 10 80 88 8
cert_cellTest_block 2560 11 88 96 8
cert_cellTest_block 2560 12 96 104 8
cert_cellTest_block 2560 13 104 112 8
cert_cellTest_block 2560 14 112 120 8
cert_cellTest_block 2560 15 120 128 8
cert_cellTest_block 2560 16 128 136 8
cert_cellTest_block 2560 17 136 144 8
cert_cellTest_block 2560 18 144 152 8
cert_cellTest_block 2560 19 152 160 8
cert_cellTest_block 2560 20 160 168 8
cert_cellTest_block 2560 21 168 176 8
cert_cellTest_block 2560 22 176 184 8
cert_cellTest_block 2560 23 184 192 8
cert_cellTest_block 2560 24 192 200 8
cert_cellTest_block 2560 25 200 208 8
cert_cellTest_block 2560 26 208 216 8
cert_cellTest_block 2560 27 216 224 8
cert_cellTest_block 2560 28 224 232 8
cert_cellTest_block 2560 29 232 240 8
cert_cellTest_block 2560 30 240 248 8
cert_cellTest_block 2560 31 248 256 8
theorem cellTest_2560_complete : Interval cellTest_2560 0 256 :=
  (interval_append cellTest_2560 0 128 256
  (interval_append cellTest_2560 0 64 128
  (interval_append cellTest_2560 0 32 64
  (interval_append cellTest_2560 0 16 32
  (interval_append cellTest_2560 0 8 16
  cellTest_2560_block_0
  cellTest_2560_block_1)
  (interval_append cellTest_2560 16 24 32
  cellTest_2560_block_2
  cellTest_2560_block_3))
  (interval_append cellTest_2560 32 48 64
  (interval_append cellTest_2560 32 40 48
  cellTest_2560_block_4
  cellTest_2560_block_5)
  (interval_append cellTest_2560 48 56 64
  cellTest_2560_block_6
  cellTest_2560_block_7)))
  (interval_append cellTest_2560 64 96 128
  (interval_append cellTest_2560 64 80 96
  (interval_append cellTest_2560 64 72 80
  cellTest_2560_block_8
  cellTest_2560_block_9)
  (interval_append cellTest_2560 80 88 96
  cellTest_2560_block_10
  cellTest_2560_block_11))
  (interval_append cellTest_2560 96 112 128
  (interval_append cellTest_2560 96 104 112
  cellTest_2560_block_12
  cellTest_2560_block_13)
  (interval_append cellTest_2560 112 120 128
  cellTest_2560_block_14
  cellTest_2560_block_15))))
  (interval_append cellTest_2560 128 192 256
  (interval_append cellTest_2560 128 160 192
  (interval_append cellTest_2560 128 144 160
  (interval_append cellTest_2560 128 136 144
  cellTest_2560_block_16
  cellTest_2560_block_17)
  (interval_append cellTest_2560 144 152 160
  cellTest_2560_block_18
  cellTest_2560_block_19))
  (interval_append cellTest_2560 160 176 192
  (interval_append cellTest_2560 160 168 176
  cellTest_2560_block_20
  cellTest_2560_block_21)
  (interval_append cellTest_2560 176 184 192
  cellTest_2560_block_22
  cellTest_2560_block_23)))
  (interval_append cellTest_2560 192 224 256
  (interval_append cellTest_2560 192 208 224
  (interval_append cellTest_2560 192 200 208
  cellTest_2560_block_24
  cellTest_2560_block_25)
  (interval_append cellTest_2560 208 216 224
  cellTest_2560_block_26
  cellTest_2560_block_27))
  (interval_append cellTest_2560 224 240 256
  (interval_append cellTest_2560 224 232 240
  cellTest_2560_block_28
  cellTest_2560_block_29)
  (interval_append cellTest_2560 240 248 256
  cellTest_2560_block_30
  cellTest_2560_block_31)))))
cert_cellTestInterval 2560 2816
end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells011 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 2816
cert_cellTest_block 2816 0 0 8 8
cert_cellTest_block 2816 1 8 16 8
cert_cellTest_block 2816 2 16 24 8
cert_cellTest_block 2816 3 24 32 8
cert_cellTest_block 2816 4 32 40 8
cert_cellTest_block 2816 5 40 48 8
cert_cellTest_block 2816 6 48 56 8
cert_cellTest_block 2816 7 56 64 8
cert_cellTest_block 2816 8 64 72 8
cert_cellTest_block 2816 9 72 80 8
cert_cellTest_block 2816 10 80 88 8
cert_cellTest_block 2816 11 88 96 8
cert_cellTest_block 2816 12 96 104 8
cert_cellTest_block 2816 13 104 112 8
cert_cellTest_block 2816 14 112 120 8
cert_cellTest_block 2816 15 120 128 8
cert_cellTest_block 2816 16 128 136 8
cert_cellTest_block 2816 17 136 144 8
cert_cellTest_block 2816 18 144 152 8
cert_cellTest_block 2816 19 152 160 8
cert_cellTest_block 2816 20 160 168 8
cert_cellTest_block 2816 21 168 176 8
cert_cellTest_block 2816 22 176 184 8
cert_cellTest_block 2816 23 184 192 8
cert_cellTest_block 2816 24 192 200 8
cert_cellTest_block 2816 25 200 208 8
cert_cellTest_block 2816 26 208 216 8
cert_cellTest_block 2816 27 216 224 8
cert_cellTest_block 2816 28 224 232 8
cert_cellTest_block 2816 29 232 240 8
cert_cellTest_block 2816 30 240 248 8
cert_cellTest_block 2816 31 248 256 8
theorem cellTest_2816_complete : Interval cellTest_2816 0 256 :=
  (interval_append cellTest_2816 0 128 256
  (interval_append cellTest_2816 0 64 128
  (interval_append cellTest_2816 0 32 64
  (interval_append cellTest_2816 0 16 32
  (interval_append cellTest_2816 0 8 16
  cellTest_2816_block_0
  cellTest_2816_block_1)
  (interval_append cellTest_2816 16 24 32
  cellTest_2816_block_2
  cellTest_2816_block_3))
  (interval_append cellTest_2816 32 48 64
  (interval_append cellTest_2816 32 40 48
  cellTest_2816_block_4
  cellTest_2816_block_5)
  (interval_append cellTest_2816 48 56 64
  cellTest_2816_block_6
  cellTest_2816_block_7)))
  (interval_append cellTest_2816 64 96 128
  (interval_append cellTest_2816 64 80 96
  (interval_append cellTest_2816 64 72 80
  cellTest_2816_block_8
  cellTest_2816_block_9)
  (interval_append cellTest_2816 80 88 96
  cellTest_2816_block_10
  cellTest_2816_block_11))
  (interval_append cellTest_2816 96 112 128
  (interval_append cellTest_2816 96 104 112
  cellTest_2816_block_12
  cellTest_2816_block_13)
  (interval_append cellTest_2816 112 120 128
  cellTest_2816_block_14
  cellTest_2816_block_15))))
  (interval_append cellTest_2816 128 192 256
  (interval_append cellTest_2816 128 160 192
  (interval_append cellTest_2816 128 144 160
  (interval_append cellTest_2816 128 136 144
  cellTest_2816_block_16
  cellTest_2816_block_17)
  (interval_append cellTest_2816 144 152 160
  cellTest_2816_block_18
  cellTest_2816_block_19))
  (interval_append cellTest_2816 160 176 192
  (interval_append cellTest_2816 160 168 176
  cellTest_2816_block_20
  cellTest_2816_block_21)
  (interval_append cellTest_2816 176 184 192
  cellTest_2816_block_22
  cellTest_2816_block_23)))
  (interval_append cellTest_2816 192 224 256
  (interval_append cellTest_2816 192 208 224
  (interval_append cellTest_2816 192 200 208
  cellTest_2816_block_24
  cellTest_2816_block_25)
  (interval_append cellTest_2816 208 216 224
  cellTest_2816_block_26
  cellTest_2816_block_27))
  (interval_append cellTest_2816 224 240 256
  (interval_append cellTest_2816 224 232 240
  cellTest_2816_block_28
  cellTest_2816_block_29)
  (interval_append cellTest_2816 240 248 256
  cellTest_2816_block_30
  cellTest_2816_block_31)))))
cert_cellTestInterval 2816 3072
end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheCells012 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_cellTest 3072
cert_cellTest_block 3072 0 0 8 8
cert_cellTest_block 3072 1 8 16 8
cert_cellTest_block 3072 2 16 24 8
cert_cellTest_block 3072 3 24 32 8
cert_cellTest_block 3072 4 32 40 8
cert_cellTest_block 3072 5 40 48 8
cert_cellTest_block 3072 6 48 56 8
cert_cellTest_block 3072 7 56 64 8
cert_cellTest_block 3072 8 64 72 8
cert_cellTest_block 3072 9 72 78 6
cert_cellTest_complete_3 3072 78
cert_cellTestInterval 3072 3150
end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheBad000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheBad001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheBad002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
