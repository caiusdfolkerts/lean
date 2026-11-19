module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra00GrowthCacheRidgeSupport7Part000
public import RootedSixExtra00GrowthCacheRidgeSupport7Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 7 015 14
cert_ridgeSupport_suffix_decode_4 7 014 14 13 13 015 015 0
cert_ridgeSupport_suffix_decode_4 7 013 14 45 32 015 014 13
cert_ridgeSupport_suffix_decode_4 7 012 14 77 32 015 013 45
cert_ridgeSupport_suffix_decode_4 7 011 14 109 32 015 012 77
cert_ridgeSupport_suffix_decode_4 7 010 14 141 32 015 011 109
cert_ridgeSupport_suffix_decode_4 7 009 14 173 32 015 010 141
cert_ridgeSupport_suffix_decode_4 7 008 14 205 32 015 009 173
cert_ridgeSupport_suffix_decode_4 7 007 14 237 32 015 008 205
cert_ridgeSupport_suffix_decode_4 7 006 14 269 32 015 007 237
cert_ridgeSupport_suffix_decode_4 7 005 14 301 32 015 006 269
cert_ridgeSupport_suffix_decode_4 7 004 14 333 32 015 005 301
cert_ridgeSupport_suffix_decode_4 7 003 14 365 32 015 004 333
cert_ridgeSupport_suffix_decode_4 7 002 14 397 32 015 003 365
cert_ridgeSupport_suffix_decode_4 7 001 14 429 32 015 002 397
cert_ridgeSupport_suffix_decode_4 7 000 14 461 32 015 001 429
cert_ridgeSupport_eq_4 7
theorem ridgeTest_large_7 : ridgeTest 7 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport7_eq]
    simp only [ridgeSupport7_suffix_000, ridgeSupport7_suffix_001, ridgeSupport7_suffix_002, ridgeSupport7_suffix_003, ridgeSupport7_suffix_004, ridgeSupport7_suffix_005, ridgeSupport7_suffix_006, ridgeSupport7_suffix_007, ridgeSupport7_suffix_008, ridgeSupport7_suffix_009, ridgeSupport7_suffix_010, ridgeSupport7_suffix_011, ridgeSupport7_suffix_012, ridgeSupport7_suffix_013, ridgeSupport7_suffix_014, ridgeSupport7_suffix_015, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport7_000_mask, ridgeSupport7_001_mask, ridgeSupport7_002_mask, ridgeSupport7_003_mask, ridgeSupport7_004_mask, ridgeSupport7_005_mask, ridgeSupport7_006_mask, ridgeSupport7_007_mask, ridgeSupport7_008_mask, ridgeSupport7_009_mask, ridgeSupport7_010_mask, ridgeSupport7_011_mask, ridgeSupport7_012_mask, ridgeSupport7_013_mask, ridgeSupport7_014_mask]
    decide +kernel
  · rw [ridgeSupport7_eq]
    simp only [ridgeSupport7_suffix_000, ridgeSupport7_suffix_001, ridgeSupport7_suffix_002, ridgeSupport7_suffix_003, ridgeSupport7_suffix_004, ridgeSupport7_suffix_005, ridgeSupport7_suffix_006, ridgeSupport7_suffix_007, ridgeSupport7_suffix_008, ridgeSupport7_suffix_009, ridgeSupport7_suffix_010, ridgeSupport7_suffix_011, ridgeSupport7_suffix_012, ridgeSupport7_suffix_013, ridgeSupport7_suffix_014, ridgeSupport7_suffix_015, List.all_append, List.all_nil, ridgeSupport7_000_checked, ridgeSupport7_001_checked, ridgeSupport7_002_checked, ridgeSupport7_003_checked, ridgeSupport7_004_checked, ridgeSupport7_005_checked, ridgeSupport7_006_checked, ridgeSupport7_007_checked, ridgeSupport7_008_checked, ridgeSupport7_009_checked, ridgeSupport7_010_checked, ridgeSupport7_011_checked, ridgeSupport7_012_checked, ridgeSupport7_013_checked, ridgeSupport7_014_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
