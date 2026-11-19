module
prelude
public meta import LowerSchemas.BundledChecks
public import RootedSixExtra05GrowthCacheData

/- RootedSixExtra05GrowthCacheBad007 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheBad008 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
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
cert_badTest_block 2048 15 120 122 2
theorem badTest_2048_complete : Interval badTest_2048 0 122 :=
  (interval_append badTest_2048 0 64 122
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
  (interval_append badTest_2048 64 96 122
  (interval_append badTest_2048 64 80 96
  (interval_append badTest_2048 64 72 80
  badTest_2048_block_8
  badTest_2048_block_9)
  (interval_append badTest_2048 80 88 96
  badTest_2048_block_10
  badTest_2048_block_11))
  (interval_append badTest_2048 96 112 122
  (interval_append badTest_2048 96 104 112
  badTest_2048_block_12
  badTest_2048_block_13)
  (interval_append badTest_2048 112 120 122
  badTest_2048_block_14
  badTest_2048_block_15))))
cert_badTestInterval 2048 2170
end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheRidges000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheRidges001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheRidges002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheRidges004 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheWellFormed000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheWellFormed001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheWellFormed002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheWellFormed003 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheWellFormed004 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheWellFormed005 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheWellFormed006 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheWellFormed007 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
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
end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
/- RootedSixExtra05GrowthCacheWellFormed008 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth RawNatGrowthSoundness RawGrowthCacheCertificate FiniteChecks
cert_wellFormedTest 2048
cert_wellFormedTest_block 2048 0 0 16 16
cert_wellFormedTest_block 2048 1 16 32 16
cert_wellFormedTest_block 2048 2 32 48 16
cert_wellFormedTest_block 2048 3 48 64 16
cert_wellFormedTest_block 2048 4 64 80 16
cert_wellFormedTest_block 2048 5 80 96 16
cert_wellFormedTest_block 2048 6 96 112 16
cert_wellFormedTest_block 2048 7 112 122 10
theorem wellFormedTest_2048_complete : Interval wellFormedTest_2048 0 122 :=
  (interval_append wellFormedTest_2048 0 64 122
  (interval_append wellFormedTest_2048 0 32 64
  (interval_append wellFormedTest_2048 0 16 32
  wellFormedTest_2048_block_0
  wellFormedTest_2048_block_1)
  (interval_append wellFormedTest_2048 32 48 64
  wellFormedTest_2048_block_2
  wellFormedTest_2048_block_3))
  (interval_append wellFormedTest_2048 64 96 122
  (interval_append wellFormedTest_2048 64 80 96
  wellFormedTest_2048_block_4
  wellFormedTest_2048_block_5)
  (interval_append wellFormedTest_2048 96 112 122
  wellFormedTest_2048_block_6
  wellFormedTest_2048_block_7)))
cert_wellFormedTestInterval 2048 2170
end Papers.RationalityTen.RootedCaches.RootedSixExtra05

end
end
