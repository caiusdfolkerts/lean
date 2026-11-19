module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra00GrowthCacheRidgeSupport52Part000
public import RootedSixExtra00GrowthCacheRidgeSupport52Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 52 015 14
cert_ridgeSupport_suffix_decode_4 52 014 14 13 13 015 015 0
cert_ridgeSupport_suffix_decode_4 52 013 14 45 32 015 014 13
cert_ridgeSupport_suffix_decode_4 52 012 14 77 32 015 013 45
cert_ridgeSupport_suffix_decode_4 52 011 14 109 32 015 012 77
cert_ridgeSupport_suffix_decode_4 52 010 14 141 32 015 011 109
cert_ridgeSupport_suffix_decode_4 52 009 14 173 32 015 010 141
cert_ridgeSupport_suffix_decode_4 52 008 14 205 32 015 009 173
cert_ridgeSupport_suffix_decode_4 52 007 14 237 32 015 008 205
cert_ridgeSupport_suffix_decode_4 52 006 14 269 32 015 007 237
cert_ridgeSupport_suffix_decode_4 52 005 14 301 32 015 006 269
cert_ridgeSupport_suffix_decode_4 52 004 14 333 32 015 005 301
cert_ridgeSupport_suffix_decode_4 52 003 14 365 32 015 004 333
cert_ridgeSupport_suffix_decode_4 52 002 14 397 32 015 003 365
cert_ridgeSupport_suffix_decode_4 52 001 14 429 32 015 002 397
cert_ridgeSupport_suffix_decode_4 52 000 14 461 32 015 001 429
cert_ridgeSupport_eq_4 52
theorem ridgeTest_large_52 : ridgeTest 52 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport52_eq]
    simp only [ridgeSupport52_suffix_000, ridgeSupport52_suffix_001, ridgeSupport52_suffix_002, ridgeSupport52_suffix_003, ridgeSupport52_suffix_004, ridgeSupport52_suffix_005, ridgeSupport52_suffix_006, ridgeSupport52_suffix_007, ridgeSupport52_suffix_008, ridgeSupport52_suffix_009, ridgeSupport52_suffix_010, ridgeSupport52_suffix_011, ridgeSupport52_suffix_012, ridgeSupport52_suffix_013, ridgeSupport52_suffix_014, ridgeSupport52_suffix_015, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport52_000_mask, ridgeSupport52_001_mask, ridgeSupport52_002_mask, ridgeSupport52_003_mask, ridgeSupport52_004_mask, ridgeSupport52_005_mask, ridgeSupport52_006_mask, ridgeSupport52_007_mask, ridgeSupport52_008_mask, ridgeSupport52_009_mask, ridgeSupport52_010_mask, ridgeSupport52_011_mask, ridgeSupport52_012_mask, ridgeSupport52_013_mask, ridgeSupport52_014_mask]
    decide +kernel
  · rw [ridgeSupport52_eq]
    simp only [ridgeSupport52_suffix_000, ridgeSupport52_suffix_001, ridgeSupport52_suffix_002, ridgeSupport52_suffix_003, ridgeSupport52_suffix_004, ridgeSupport52_suffix_005, ridgeSupport52_suffix_006, ridgeSupport52_suffix_007, ridgeSupport52_suffix_008, ridgeSupport52_suffix_009, ridgeSupport52_suffix_010, ridgeSupport52_suffix_011, ridgeSupport52_suffix_012, ridgeSupport52_suffix_013, ridgeSupport52_suffix_014, ridgeSupport52_suffix_015, List.all_append, List.all_nil, ridgeSupport52_000_checked, ridgeSupport52_001_checked, ridgeSupport52_002_checked, ridgeSupport52_003_checked, ridgeSupport52_004_checked, ridgeSupport52_005_checked, ridgeSupport52_006_checked, ridgeSupport52_007_checked, ridgeSupport52_008_checked, ridgeSupport52_009_checked, ridgeSupport52_010_checked, ridgeSupport52_011_checked, ridgeSupport52_012_checked, ridgeSupport52_013_checked, ridgeSupport52_014_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
