module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra00GrowthCacheRidgeSupport13Part000
public import RootedSixExtra00GrowthCacheRidgeSupport13Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 13 015 14
cert_ridgeSupport_suffix_decode_4 13 014 14 13 13 015 015 0
cert_ridgeSupport_suffix_decode_4 13 013 14 45 32 015 014 13
cert_ridgeSupport_suffix_decode_4 13 012 14 77 32 015 013 45
cert_ridgeSupport_suffix_decode_4 13 011 14 109 32 015 012 77
cert_ridgeSupport_suffix_decode_4 13 010 14 141 32 015 011 109
cert_ridgeSupport_suffix_decode_4 13 009 14 173 32 015 010 141
cert_ridgeSupport_suffix_decode_4 13 008 14 205 32 015 009 173
cert_ridgeSupport_suffix_decode_4 13 007 14 237 32 015 008 205
cert_ridgeSupport_suffix_decode_4 13 006 14 269 32 015 007 237
cert_ridgeSupport_suffix_decode_4 13 005 14 301 32 015 006 269
cert_ridgeSupport_suffix_decode_4 13 004 14 333 32 015 005 301
cert_ridgeSupport_suffix_decode_4 13 003 14 365 32 015 004 333
cert_ridgeSupport_suffix_decode_4 13 002 14 397 32 015 003 365
cert_ridgeSupport_suffix_decode_4 13 001 14 429 32 015 002 397
cert_ridgeSupport_suffix_decode_4 13 000 14 461 32 015 001 429
cert_ridgeSupport_eq_4 13
theorem ridgeTest_large_13 : ridgeTest 13 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport13_eq]
    simp only [ridgeSupport13_suffix_000, ridgeSupport13_suffix_001, ridgeSupport13_suffix_002, ridgeSupport13_suffix_003, ridgeSupport13_suffix_004, ridgeSupport13_suffix_005, ridgeSupport13_suffix_006, ridgeSupport13_suffix_007, ridgeSupport13_suffix_008, ridgeSupport13_suffix_009, ridgeSupport13_suffix_010, ridgeSupport13_suffix_011, ridgeSupport13_suffix_012, ridgeSupport13_suffix_013, ridgeSupport13_suffix_014, ridgeSupport13_suffix_015, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport13_000_mask, ridgeSupport13_001_mask, ridgeSupport13_002_mask, ridgeSupport13_003_mask, ridgeSupport13_004_mask, ridgeSupport13_005_mask, ridgeSupport13_006_mask, ridgeSupport13_007_mask, ridgeSupport13_008_mask, ridgeSupport13_009_mask, ridgeSupport13_010_mask, ridgeSupport13_011_mask, ridgeSupport13_012_mask, ridgeSupport13_013_mask, ridgeSupport13_014_mask]
    decide +kernel
  · rw [ridgeSupport13_eq]
    simp only [ridgeSupport13_suffix_000, ridgeSupport13_suffix_001, ridgeSupport13_suffix_002, ridgeSupport13_suffix_003, ridgeSupport13_suffix_004, ridgeSupport13_suffix_005, ridgeSupport13_suffix_006, ridgeSupport13_suffix_007, ridgeSupport13_suffix_008, ridgeSupport13_suffix_009, ridgeSupport13_suffix_010, ridgeSupport13_suffix_011, ridgeSupport13_suffix_012, ridgeSupport13_suffix_013, ridgeSupport13_suffix_014, ridgeSupport13_suffix_015, List.all_append, List.all_nil, ridgeSupport13_000_checked, ridgeSupport13_001_checked, ridgeSupport13_002_checked, ridgeSupport13_003_checked, ridgeSupport13_004_checked, ridgeSupport13_005_checked, ridgeSupport13_006_checked, ridgeSupport13_007_checked, ridgeSupport13_008_checked, ridgeSupport13_009_checked, ridgeSupport13_010_checked, ridgeSupport13_011_checked, ridgeSupport13_012_checked, ridgeSupport13_013_checked, ridgeSupport13_014_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
