module
prelude
public meta import LowerSchemas.BundledChecks
public import RootedSixExtra02GrowthCacheData

/- RootedSixExtra02GrowthCacheBad022 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad023 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad024 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheBad025 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
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
cert_badTest_block 6400 27 216 220 4
theorem badTest_6400_complete : Interval badTest_6400 0 220 :=
  (interval_append badTest_6400 0 112 220
  (interval_append badTest_6400 0 56 112
  (interval_append badTest_6400 0 24 56
  (interval_append badTest_6400 0 8 24
  badTest_6400_block_0
  (interval_append badTest_6400 8 16 24
  badTest_6400_block_1
  badTest_6400_block_2))
  (interval_append badTest_6400 24 40 56
  (interval_append badTest_6400 24 32 40
  badTest_6400_block_3
  badTest_6400_block_4)
  (interval_append badTest_6400 40 48 56
  badTest_6400_block_5
  badTest_6400_block_6)))
  (interval_append badTest_6400 56 80 112
  (interval_append badTest_6400 56 64 80
  badTest_6400_block_7
  (interval_append badTest_6400 64 72 80
  badTest_6400_block_8
  badTest_6400_block_9))
  (interval_append badTest_6400 80 96 112
  (interval_append badTest_6400 80 88 96
  badTest_6400_block_10
  badTest_6400_block_11)
  (interval_append badTest_6400 96 104 112
  badTest_6400_block_12
  badTest_6400_block_13))))
  (interval_append badTest_6400 112 168 220
  (interval_append badTest_6400 112 136 168
  (interval_append badTest_6400 112 120 136
  badTest_6400_block_14
  (interval_append badTest_6400 120 128 136
  badTest_6400_block_15
  badTest_6400_block_16))
  (interval_append badTest_6400 136 152 168
  (interval_append badTest_6400 136 144 152
  badTest_6400_block_17
  badTest_6400_block_18)
  (interval_append badTest_6400 152 160 168
  badTest_6400_block_19
  badTest_6400_block_20)))
  (interval_append badTest_6400 168 192 220
  (interval_append badTest_6400 168 176 192
  badTest_6400_block_21
  (interval_append badTest_6400 176 184 192
  badTest_6400_block_22
  badTest_6400_block_23))
  (interval_append badTest_6400 192 208 220
  (interval_append badTest_6400 192 200 208
  badTest_6400_block_24
  badTest_6400_block_25)
  (interval_append badTest_6400 208 216 220
  badTest_6400_block_26
  badTest_6400_block_27)))))
cert_badTestInterval 6400 6620
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed003 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed004 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest 1024
cert_wellFormedTest_block 1024 0 0 16 16
cert_wellFormedTest_block 1024 1 16 32 16
cert_wellFormedTest_block 1024 2 32 48 16
cert_wellFormedTest_block 1024 3 48 64 16
cert_wellFormedTest_block 1024 4 64 80 16
cert_wellFormedTest_block 1024 5 80 96 16
cert_wellFormedTest_block 1024 6 96 112 16
cert_wellFormedTest_block 1024 7 112 128 16
cert_wellFormedTest_block 1024 8 128 144 16
cert_wellFormedTest_block 1024 9 144 160 16
cert_wellFormedTest_block 1024 10 160 176 16
cert_wellFormedTest_block 1024 11 176 192 16
cert_wellFormedTest_block 1024 12 192 208 16
cert_wellFormedTest_block 1024 13 208 224 16
cert_wellFormedTest_block 1024 14 224 240 16
cert_wellFormedTest_block 1024 15 240 256 16
cert_wellFormedTest_complete 1024 256
cert_wellFormedTestInterval 1024 1280
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed005 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest 1280
cert_wellFormedTest_block 1280 0 0 16 16
cert_wellFormedTest_block 1280 1 16 32 16
cert_wellFormedTest_block 1280 2 32 48 16
cert_wellFormedTest_block 1280 3 48 64 16
cert_wellFormedTest_block 1280 4 64 80 16
cert_wellFormedTest_block 1280 5 80 96 16
cert_wellFormedTest_block 1280 6 96 112 16
cert_wellFormedTest_block 1280 7 112 128 16
cert_wellFormedTest_block 1280 8 128 144 16
cert_wellFormedTest_block 1280 9 144 160 16
cert_wellFormedTest_block 1280 10 160 176 16
cert_wellFormedTest_block 1280 11 176 192 16
cert_wellFormedTest_block 1280 12 192 208 16
cert_wellFormedTest_block 1280 13 208 224 16
cert_wellFormedTest_block 1280 14 224 240 16
cert_wellFormedTest_block 1280 15 240 256 16
cert_wellFormedTest_complete 1280 256
cert_wellFormedTestInterval 1280 1536
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed006 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest 1536
cert_wellFormedTest_block 1536 0 0 16 16
cert_wellFormedTest_block 1536 1 16 32 16
cert_wellFormedTest_block 1536 2 32 48 16
cert_wellFormedTest_block 1536 3 48 64 16
cert_wellFormedTest_block 1536 4 64 80 16
cert_wellFormedTest_block 1536 5 80 96 16
cert_wellFormedTest_block 1536 6 96 112 16
cert_wellFormedTest_block 1536 7 112 128 16
cert_wellFormedTest_block 1536 8 128 144 16
cert_wellFormedTest_block 1536 9 144 160 16
cert_wellFormedTest_block 1536 10 160 176 16
cert_wellFormedTest_block 1536 11 176 192 16
cert_wellFormedTest_block 1536 12 192 208 16
cert_wellFormedTest_block 1536 13 208 224 16
cert_wellFormedTest_block 1536 14 224 240 16
cert_wellFormedTest_block 1536 15 240 256 16
cert_wellFormedTest_complete 1536 256
cert_wellFormedTestInterval 1536 1792
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed007 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest 1792
cert_wellFormedTest_block 1792 0 0 16 16
cert_wellFormedTest_block 1792 1 16 32 16
cert_wellFormedTest_block 1792 2 32 48 16
cert_wellFormedTest_block 1792 3 48 64 16
cert_wellFormedTest_block 1792 4 64 80 16
cert_wellFormedTest_block 1792 5 80 96 16
cert_wellFormedTest_block 1792 6 96 112 16
cert_wellFormedTest_block 1792 7 112 128 16
cert_wellFormedTest_block 1792 8 128 144 16
cert_wellFormedTest_block 1792 9 144 160 16
cert_wellFormedTest_block 1792 10 160 176 16
cert_wellFormedTest_block 1792 11 176 192 16
cert_wellFormedTest_block 1792 12 192 208 16
cert_wellFormedTest_block 1792 13 208 224 16
cert_wellFormedTest_block 1792 14 224 240 16
cert_wellFormedTest_block 1792 15 240 256 16
cert_wellFormedTest_complete 1792 256
cert_wellFormedTestInterval 1792 2048
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed008 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest 2048
cert_wellFormedTest_block 2048 0 0 16 16
cert_wellFormedTest_block 2048 1 16 32 16
cert_wellFormedTest_block 2048 2 32 48 16
cert_wellFormedTest_block 2048 3 48 64 16
cert_wellFormedTest_block 2048 4 64 80 16
cert_wellFormedTest_block 2048 5 80 96 16
cert_wellFormedTest_block 2048 6 96 112 16
cert_wellFormedTest_block 2048 7 112 128 16
cert_wellFormedTest_block 2048 8 128 144 16
cert_wellFormedTest_block 2048 9 144 160 16
cert_wellFormedTest_block 2048 10 160 176 16
cert_wellFormedTest_block 2048 11 176 192 16
cert_wellFormedTest_block 2048 12 192 208 16
cert_wellFormedTest_block 2048 13 208 224 16
cert_wellFormedTest_block 2048 14 224 240 16
cert_wellFormedTest_block 2048 15 240 256 16
cert_wellFormedTest_complete 2048 256
cert_wellFormedTestInterval 2048 2304
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed009 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest 2304
cert_wellFormedTest_block 2304 0 0 16 16
cert_wellFormedTest_block 2304 1 16 32 16
cert_wellFormedTest_block 2304 2 32 48 16
cert_wellFormedTest_block 2304 3 48 64 16
cert_wellFormedTest_block 2304 4 64 80 16
cert_wellFormedTest_block 2304 5 80 96 16
cert_wellFormedTest_block 2304 6 96 112 16
cert_wellFormedTest_block 2304 7 112 128 16
cert_wellFormedTest_block 2304 8 128 144 16
cert_wellFormedTest_block 2304 9 144 160 16
cert_wellFormedTest_block 2304 10 160 176 16
cert_wellFormedTest_block 2304 11 176 192 16
cert_wellFormedTest_block 2304 12 192 208 16
cert_wellFormedTest_block 2304 13 208 224 16
cert_wellFormedTest_block 2304 14 224 240 16
cert_wellFormedTest_block 2304 15 240 256 16
cert_wellFormedTest_complete 2304 256
cert_wellFormedTestInterval 2304 2560
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed010 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest 2560
cert_wellFormedTest_block 2560 0 0 16 16
cert_wellFormedTest_block 2560 1 16 32 16
cert_wellFormedTest_block 2560 2 32 48 16
cert_wellFormedTest_block 2560 3 48 64 16
cert_wellFormedTest_block 2560 4 64 80 16
cert_wellFormedTest_block 2560 5 80 96 16
cert_wellFormedTest_block 2560 6 96 112 16
cert_wellFormedTest_block 2560 7 112 128 16
cert_wellFormedTest_block 2560 8 128 144 16
cert_wellFormedTest_block 2560 9 144 160 16
cert_wellFormedTest_block 2560 10 160 176 16
cert_wellFormedTest_block 2560 11 176 192 16
cert_wellFormedTest_block 2560 12 192 208 16
cert_wellFormedTest_block 2560 13 208 224 16
cert_wellFormedTest_block 2560 14 224 240 16
cert_wellFormedTest_block 2560 15 240 256 16
cert_wellFormedTest_complete 2560 256
cert_wellFormedTestInterval 2560 2816
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
/- RootedSixExtra02GrowthCacheWellFormed011 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest 2816
cert_wellFormedTest_block 2816 0 0 16 16
cert_wellFormedTest_block 2816 1 16 32 16
cert_wellFormedTest_block 2816 2 32 48 16
cert_wellFormedTest_block 2816 3 48 64 16
cert_wellFormedTest_block 2816 4 64 80 16
cert_wellFormedTest_block 2816 5 80 96 16
cert_wellFormedTest_block 2816 6 96 112 16
cert_wellFormedTest_block 2816 7 112 128 16
cert_wellFormedTest_block 2816 8 128 144 16
cert_wellFormedTest_block 2816 9 144 160 16
cert_wellFormedTest_block 2816 10 160 176 16
cert_wellFormedTest_block 2816 11 176 192 16
cert_wellFormedTest_block 2816 12 192 208 16
cert_wellFormedTest_block 2816 13 208 224 16
cert_wellFormedTest_block 2816 14 224 240 16
cert_wellFormedTest_block 2816 15 240 256 16
cert_wellFormedTest_complete 2816 256
cert_wellFormedTestInterval 2816 3072
end Papers.RationalityTen.RootedCaches.RootedSixExtra02

end
end
