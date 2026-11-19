module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra00GrowthCacheRidgeSupport26Part000
public import RootedSixExtra00GrowthCacheRidgeSupport26Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 26 015 14
cert_ridgeSupport_suffix_decode_4 26 014 14 13 13 015 015 0
cert_ridgeSupport_suffix_decode_4 26 013 14 45 32 015 014 13
cert_ridgeSupport_suffix_decode_4 26 012 14 77 32 015 013 45
cert_ridgeSupport_suffix_decode_4 26 011 14 109 32 015 012 77
cert_ridgeSupport_suffix_decode_4 26 010 14 141 32 015 011 109
cert_ridgeSupport_suffix_decode_4 26 009 14 173 32 015 010 141
cert_ridgeSupport_suffix_decode_4 26 008 14 205 32 015 009 173
cert_ridgeSupport_suffix_decode_4 26 007 14 237 32 015 008 205
cert_ridgeSupport_suffix_decode_4 26 006 14 269 32 015 007 237
cert_ridgeSupport_suffix_decode_4 26 005 14 301 32 015 006 269
cert_ridgeSupport_suffix_decode_4 26 004 14 333 32 015 005 301
cert_ridgeSupport_suffix_decode_4 26 003 14 365 32 015 004 333
cert_ridgeSupport_suffix_decode_4 26 002 14 397 32 015 003 365
cert_ridgeSupport_suffix_decode_4 26 001 14 429 32 015 002 397
cert_ridgeSupport_suffix_decode_4 26 000 14 461 32 015 001 429
cert_ridgeSupport_eq_4 26
theorem ridgeTest_large_26 : ridgeTest 26 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport26_eq]
    simp only [ridgeSupport26_suffix_000, ridgeSupport26_suffix_001, ridgeSupport26_suffix_002, ridgeSupport26_suffix_003, ridgeSupport26_suffix_004, ridgeSupport26_suffix_005, ridgeSupport26_suffix_006, ridgeSupport26_suffix_007, ridgeSupport26_suffix_008, ridgeSupport26_suffix_009, ridgeSupport26_suffix_010, ridgeSupport26_suffix_011, ridgeSupport26_suffix_012, ridgeSupport26_suffix_013, ridgeSupport26_suffix_014, ridgeSupport26_suffix_015, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport26_000_mask, ridgeSupport26_001_mask, ridgeSupport26_002_mask, ridgeSupport26_003_mask, ridgeSupport26_004_mask, ridgeSupport26_005_mask, ridgeSupport26_006_mask, ridgeSupport26_007_mask, ridgeSupport26_008_mask, ridgeSupport26_009_mask, ridgeSupport26_010_mask, ridgeSupport26_011_mask, ridgeSupport26_012_mask, ridgeSupport26_013_mask, ridgeSupport26_014_mask]
    decide +kernel
  · rw [ridgeSupport26_eq]
    simp only [ridgeSupport26_suffix_000, ridgeSupport26_suffix_001, ridgeSupport26_suffix_002, ridgeSupport26_suffix_003, ridgeSupport26_suffix_004, ridgeSupport26_suffix_005, ridgeSupport26_suffix_006, ridgeSupport26_suffix_007, ridgeSupport26_suffix_008, ridgeSupport26_suffix_009, ridgeSupport26_suffix_010, ridgeSupport26_suffix_011, ridgeSupport26_suffix_012, ridgeSupport26_suffix_013, ridgeSupport26_suffix_014, ridgeSupport26_suffix_015, List.all_append, List.all_nil, ridgeSupport26_000_checked, ridgeSupport26_001_checked, ridgeSupport26_002_checked, ridgeSupport26_003_checked, ridgeSupport26_004_checked, ridgeSupport26_005_checked, ridgeSupport26_006_checked, ridgeSupport26_007_checked, ridgeSupport26_008_checked, ridgeSupport26_009_checked, ridgeSupport26_010_checked, ridgeSupport26_011_checked, ridgeSupport26_012_checked, ridgeSupport26_013_checked, ridgeSupport26_014_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
