module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra00GrowthCacheRidgeSupport44Part000
public import RootedSixExtra00GrowthCacheRidgeSupport44Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 44 015 14
cert_ridgeSupport_suffix_decode_4 44 014 14 13 13 015 015 0
cert_ridgeSupport_suffix_decode_4 44 013 14 45 32 015 014 13
cert_ridgeSupport_suffix_decode_4 44 012 14 77 32 015 013 45
cert_ridgeSupport_suffix_decode_4 44 011 14 109 32 015 012 77
cert_ridgeSupport_suffix_decode_4 44 010 14 141 32 015 011 109
cert_ridgeSupport_suffix_decode_4 44 009 14 173 32 015 010 141
cert_ridgeSupport_suffix_decode_4 44 008 14 205 32 015 009 173
cert_ridgeSupport_suffix_decode_4 44 007 14 237 32 015 008 205
cert_ridgeSupport_suffix_decode_4 44 006 14 269 32 015 007 237
cert_ridgeSupport_suffix_decode_4 44 005 14 301 32 015 006 269
cert_ridgeSupport_suffix_decode_4 44 004 14 333 32 015 005 301
cert_ridgeSupport_suffix_decode_4 44 003 14 365 32 015 004 333
cert_ridgeSupport_suffix_decode_4 44 002 14 397 32 015 003 365
cert_ridgeSupport_suffix_decode_4 44 001 14 429 32 015 002 397
cert_ridgeSupport_suffix_decode_4 44 000 14 461 32 015 001 429
cert_ridgeSupport_eq_4 44
theorem ridgeTest_large_44 : ridgeTest 44 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport44_eq]
    simp only [ridgeSupport44_suffix_000, ridgeSupport44_suffix_001, ridgeSupport44_suffix_002, ridgeSupport44_suffix_003, ridgeSupport44_suffix_004, ridgeSupport44_suffix_005, ridgeSupport44_suffix_006, ridgeSupport44_suffix_007, ridgeSupport44_suffix_008, ridgeSupport44_suffix_009, ridgeSupport44_suffix_010, ridgeSupport44_suffix_011, ridgeSupport44_suffix_012, ridgeSupport44_suffix_013, ridgeSupport44_suffix_014, ridgeSupport44_suffix_015, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport44_000_mask, ridgeSupport44_001_mask, ridgeSupport44_002_mask, ridgeSupport44_003_mask, ridgeSupport44_004_mask, ridgeSupport44_005_mask, ridgeSupport44_006_mask, ridgeSupport44_007_mask, ridgeSupport44_008_mask, ridgeSupport44_009_mask, ridgeSupport44_010_mask, ridgeSupport44_011_mask, ridgeSupport44_012_mask, ridgeSupport44_013_mask, ridgeSupport44_014_mask]
    decide +kernel
  · rw [ridgeSupport44_eq]
    simp only [ridgeSupport44_suffix_000, ridgeSupport44_suffix_001, ridgeSupport44_suffix_002, ridgeSupport44_suffix_003, ridgeSupport44_suffix_004, ridgeSupport44_suffix_005, ridgeSupport44_suffix_006, ridgeSupport44_suffix_007, ridgeSupport44_suffix_008, ridgeSupport44_suffix_009, ridgeSupport44_suffix_010, ridgeSupport44_suffix_011, ridgeSupport44_suffix_012, ridgeSupport44_suffix_013, ridgeSupport44_suffix_014, ridgeSupport44_suffix_015, List.all_append, List.all_nil, ridgeSupport44_000_checked, ridgeSupport44_001_checked, ridgeSupport44_002_checked, ridgeSupport44_003_checked, ridgeSupport44_004_checked, ridgeSupport44_005_checked, ridgeSupport44_006_checked, ridgeSupport44_007_checked, ridgeSupport44_008_checked, ridgeSupport44_009_checked, ridgeSupport44_010_checked, ridgeSupport44_011_checked, ridgeSupport44_012_checked, ridgeSupport44_013_checked, ridgeSupport44_014_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
