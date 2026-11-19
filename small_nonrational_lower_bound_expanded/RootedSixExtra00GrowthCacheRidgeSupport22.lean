module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra00GrowthCacheRidgeSupport22Part000
public import RootedSixExtra00GrowthCacheRidgeSupport22Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 22 015 14
cert_ridgeSupport_suffix_decode_4 22 014 14 13 13 015 015 0
cert_ridgeSupport_suffix_decode_4 22 013 14 45 32 015 014 13
cert_ridgeSupport_suffix_decode_4 22 012 14 77 32 015 013 45
cert_ridgeSupport_suffix_decode_4 22 011 14 109 32 015 012 77
cert_ridgeSupport_suffix_decode_4 22 010 14 141 32 015 011 109
cert_ridgeSupport_suffix_decode_4 22 009 14 173 32 015 010 141
cert_ridgeSupport_suffix_decode_4 22 008 14 205 32 015 009 173
cert_ridgeSupport_suffix_decode_4 22 007 14 237 32 015 008 205
cert_ridgeSupport_suffix_decode_4 22 006 14 269 32 015 007 237
cert_ridgeSupport_suffix_decode_4 22 005 14 301 32 015 006 269
cert_ridgeSupport_suffix_decode_4 22 004 14 333 32 015 005 301
cert_ridgeSupport_suffix_decode_4 22 003 14 365 32 015 004 333
cert_ridgeSupport_suffix_decode_4 22 002 14 397 32 015 003 365
cert_ridgeSupport_suffix_decode_4 22 001 14 429 32 015 002 397
cert_ridgeSupport_suffix_decode_4 22 000 14 461 32 015 001 429
cert_ridgeSupport_eq_4 22
theorem ridgeTest_large_22 : ridgeTest 22 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport22_eq]
    simp only [ridgeSupport22_suffix_000, ridgeSupport22_suffix_001, ridgeSupport22_suffix_002, ridgeSupport22_suffix_003, ridgeSupport22_suffix_004, ridgeSupport22_suffix_005, ridgeSupport22_suffix_006, ridgeSupport22_suffix_007, ridgeSupport22_suffix_008, ridgeSupport22_suffix_009, ridgeSupport22_suffix_010, ridgeSupport22_suffix_011, ridgeSupport22_suffix_012, ridgeSupport22_suffix_013, ridgeSupport22_suffix_014, ridgeSupport22_suffix_015, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport22_000_mask, ridgeSupport22_001_mask, ridgeSupport22_002_mask, ridgeSupport22_003_mask, ridgeSupport22_004_mask, ridgeSupport22_005_mask, ridgeSupport22_006_mask, ridgeSupport22_007_mask, ridgeSupport22_008_mask, ridgeSupport22_009_mask, ridgeSupport22_010_mask, ridgeSupport22_011_mask, ridgeSupport22_012_mask, ridgeSupport22_013_mask, ridgeSupport22_014_mask]
    decide +kernel
  · rw [ridgeSupport22_eq]
    simp only [ridgeSupport22_suffix_000, ridgeSupport22_suffix_001, ridgeSupport22_suffix_002, ridgeSupport22_suffix_003, ridgeSupport22_suffix_004, ridgeSupport22_suffix_005, ridgeSupport22_suffix_006, ridgeSupport22_suffix_007, ridgeSupport22_suffix_008, ridgeSupport22_suffix_009, ridgeSupport22_suffix_010, ridgeSupport22_suffix_011, ridgeSupport22_suffix_012, ridgeSupport22_suffix_013, ridgeSupport22_suffix_014, ridgeSupport22_suffix_015, List.all_append, List.all_nil, ridgeSupport22_000_checked, ridgeSupport22_001_checked, ridgeSupport22_002_checked, ridgeSupport22_003_checked, ridgeSupport22_004_checked, ridgeSupport22_005_checked, ridgeSupport22_006_checked, ridgeSupport22_007_checked, ridgeSupport22_008_checked, ridgeSupport22_009_checked, ridgeSupport22_010_checked, ridgeSupport22_011_checked, ridgeSupport22_012_checked, ridgeSupport22_013_checked, ridgeSupport22_014_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
