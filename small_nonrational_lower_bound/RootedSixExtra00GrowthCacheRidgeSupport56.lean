module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra00GrowthCacheRidgeSupport56Part000
public import RootedSixExtra00GrowthCacheRidgeSupport56Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 56 015 14
cert_ridgeSupport_suffix_decode_4 56 014 14 13 13 015 015 0
cert_ridgeSupport_suffix_decode_4 56 013 14 45 32 015 014 13
cert_ridgeSupport_suffix_decode_4 56 012 14 77 32 015 013 45
cert_ridgeSupport_suffix_decode_4 56 011 14 109 32 015 012 77
cert_ridgeSupport_suffix_decode_4 56 010 14 141 32 015 011 109
cert_ridgeSupport_suffix_decode_4 56 009 14 173 32 015 010 141
cert_ridgeSupport_suffix_decode_4 56 008 14 205 32 015 009 173
cert_ridgeSupport_suffix_decode_4 56 007 14 237 32 015 008 205
cert_ridgeSupport_suffix_decode_4 56 006 14 269 32 015 007 237
cert_ridgeSupport_suffix_decode_4 56 005 14 301 32 015 006 269
cert_ridgeSupport_suffix_decode_4 56 004 14 333 32 015 005 301
cert_ridgeSupport_suffix_decode_4 56 003 14 365 32 015 004 333
cert_ridgeSupport_suffix_decode_4 56 002 14 397 32 015 003 365
cert_ridgeSupport_suffix_decode_4 56 001 14 429 32 015 002 397
cert_ridgeSupport_suffix_decode_4 56 000 14 461 32 015 001 429
cert_ridgeSupport_eq_4 56
theorem ridgeTest_large_56 : ridgeTest 56 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport56_eq]
    simp only [ridgeSupport56_suffix_000, ridgeSupport56_suffix_001, ridgeSupport56_suffix_002, ridgeSupport56_suffix_003, ridgeSupport56_suffix_004, ridgeSupport56_suffix_005, ridgeSupport56_suffix_006, ridgeSupport56_suffix_007, ridgeSupport56_suffix_008, ridgeSupport56_suffix_009, ridgeSupport56_suffix_010, ridgeSupport56_suffix_011, ridgeSupport56_suffix_012, ridgeSupport56_suffix_013, ridgeSupport56_suffix_014, ridgeSupport56_suffix_015, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport56_000_mask, ridgeSupport56_001_mask, ridgeSupport56_002_mask, ridgeSupport56_003_mask, ridgeSupport56_004_mask, ridgeSupport56_005_mask, ridgeSupport56_006_mask, ridgeSupport56_007_mask, ridgeSupport56_008_mask, ridgeSupport56_009_mask, ridgeSupport56_010_mask, ridgeSupport56_011_mask, ridgeSupport56_012_mask, ridgeSupport56_013_mask, ridgeSupport56_014_mask]
    decide +kernel
  · rw [ridgeSupport56_eq]
    simp only [ridgeSupport56_suffix_000, ridgeSupport56_suffix_001, ridgeSupport56_suffix_002, ridgeSupport56_suffix_003, ridgeSupport56_suffix_004, ridgeSupport56_suffix_005, ridgeSupport56_suffix_006, ridgeSupport56_suffix_007, ridgeSupport56_suffix_008, ridgeSupport56_suffix_009, ridgeSupport56_suffix_010, ridgeSupport56_suffix_011, ridgeSupport56_suffix_012, ridgeSupport56_suffix_013, ridgeSupport56_suffix_014, ridgeSupport56_suffix_015, List.all_append, List.all_nil, ridgeSupport56_000_checked, ridgeSupport56_001_checked, ridgeSupport56_002_checked, ridgeSupport56_003_checked, ridgeSupport56_004_checked, ridgeSupport56_005_checked, ridgeSupport56_006_checked, ridgeSupport56_007_checked, ridgeSupport56_008_checked, ridgeSupport56_009_checked, ridgeSupport56_010_checked, ridgeSupport56_011_checked, ridgeSupport56_012_checked, ridgeSupport56_013_checked, ridgeSupport56_014_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
