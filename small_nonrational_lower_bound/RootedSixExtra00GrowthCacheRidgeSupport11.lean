module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra00GrowthCacheRidgeSupport11Part000
public import RootedSixExtra00GrowthCacheRidgeSupport11Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 11 015 14
cert_ridgeSupport_suffix_decode_4 11 014 14 13 13 015 015 0
cert_ridgeSupport_suffix_decode_4 11 013 14 45 32 015 014 13
cert_ridgeSupport_suffix_decode_4 11 012 14 77 32 015 013 45
cert_ridgeSupport_suffix_decode_4 11 011 14 109 32 015 012 77
cert_ridgeSupport_suffix_decode_4 11 010 14 141 32 015 011 109
cert_ridgeSupport_suffix_decode_4 11 009 14 173 32 015 010 141
cert_ridgeSupport_suffix_decode_4 11 008 14 205 32 015 009 173
cert_ridgeSupport_suffix_decode_4 11 007 14 237 32 015 008 205
cert_ridgeSupport_suffix_decode_4 11 006 14 269 32 015 007 237
cert_ridgeSupport_suffix_decode_4 11 005 14 301 32 015 006 269
cert_ridgeSupport_suffix_decode_4 11 004 14 333 32 015 005 301
cert_ridgeSupport_suffix_decode_4 11 003 14 365 32 015 004 333
cert_ridgeSupport_suffix_decode_4 11 002 14 397 32 015 003 365
cert_ridgeSupport_suffix_decode_4 11 001 14 429 32 015 002 397
cert_ridgeSupport_suffix_decode_4 11 000 14 461 32 015 001 429
cert_ridgeSupport_eq_4 11
theorem ridgeTest_large_11 : ridgeTest 11 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport11_eq]
    simp only [ridgeSupport11_suffix_000, ridgeSupport11_suffix_001, ridgeSupport11_suffix_002, ridgeSupport11_suffix_003, ridgeSupport11_suffix_004, ridgeSupport11_suffix_005, ridgeSupport11_suffix_006, ridgeSupport11_suffix_007, ridgeSupport11_suffix_008, ridgeSupport11_suffix_009, ridgeSupport11_suffix_010, ridgeSupport11_suffix_011, ridgeSupport11_suffix_012, ridgeSupport11_suffix_013, ridgeSupport11_suffix_014, ridgeSupport11_suffix_015, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport11_000_mask, ridgeSupport11_001_mask, ridgeSupport11_002_mask, ridgeSupport11_003_mask, ridgeSupport11_004_mask, ridgeSupport11_005_mask, ridgeSupport11_006_mask, ridgeSupport11_007_mask, ridgeSupport11_008_mask, ridgeSupport11_009_mask, ridgeSupport11_010_mask, ridgeSupport11_011_mask, ridgeSupport11_012_mask, ridgeSupport11_013_mask, ridgeSupport11_014_mask]
    decide +kernel
  · rw [ridgeSupport11_eq]
    simp only [ridgeSupport11_suffix_000, ridgeSupport11_suffix_001, ridgeSupport11_suffix_002, ridgeSupport11_suffix_003, ridgeSupport11_suffix_004, ridgeSupport11_suffix_005, ridgeSupport11_suffix_006, ridgeSupport11_suffix_007, ridgeSupport11_suffix_008, ridgeSupport11_suffix_009, ridgeSupport11_suffix_010, ridgeSupport11_suffix_011, ridgeSupport11_suffix_012, ridgeSupport11_suffix_013, ridgeSupport11_suffix_014, ridgeSupport11_suffix_015, List.all_append, List.all_nil, ridgeSupport11_000_checked, ridgeSupport11_001_checked, ridgeSupport11_002_checked, ridgeSupport11_003_checked, ridgeSupport11_004_checked, ridgeSupport11_005_checked, ridgeSupport11_006_checked, ridgeSupport11_007_checked, ridgeSupport11_008_checked, ridgeSupport11_009_checked, ridgeSupport11_010_checked, ridgeSupport11_011_checked, ridgeSupport11_012_checked, ridgeSupport11_013_checked, ridgeSupport11_014_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
