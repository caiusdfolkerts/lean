module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra01GrowthCacheRidgeSupport448Part000
public import RootedSixExtra01GrowthCacheRidgeSupport448Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 448 014 12
cert_ridgeSupport_suffix_decode_4 448 013 12 29 29 014 014 0
cert_ridgeSupport_suffix_decode_4 448 012 12 61 32 014 013 29
cert_ridgeSupport_suffix_decode_4 448 011 12 93 32 014 012 61
cert_ridgeSupport_suffix_decode_4 448 010 12 125 32 014 011 93
cert_ridgeSupport_suffix_decode_4 448 009 12 157 32 014 010 125
cert_ridgeSupport_suffix_decode_4 448 008 12 189 32 014 009 157
cert_ridgeSupport_suffix_decode_4 448 007 12 221 32 014 008 189
cert_ridgeSupport_suffix_decode_4 448 006 12 253 32 014 007 221
cert_ridgeSupport_suffix_decode_4 448 005 12 285 32 014 006 253
cert_ridgeSupport_suffix_decode_4 448 004 12 317 32 014 005 285
cert_ridgeSupport_suffix_decode_4 448 003 12 349 32 014 004 317
cert_ridgeSupport_suffix_decode_4 448 002 12 381 32 014 003 349
cert_ridgeSupport_suffix_decode_4 448 001 12 413 32 014 002 381
cert_ridgeSupport_suffix_decode_4 448 000 12 445 32 014 001 413
cert_ridgeSupport_eq_4 448
theorem ridgeTest_large_448 : ridgeTest 448 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport448_eq]
    simp only [ridgeSupport448_suffix_000, ridgeSupport448_suffix_001, ridgeSupport448_suffix_002, ridgeSupport448_suffix_003, ridgeSupport448_suffix_004, ridgeSupport448_suffix_005, ridgeSupport448_suffix_006, ridgeSupport448_suffix_007, ridgeSupport448_suffix_008, ridgeSupport448_suffix_009, ridgeSupport448_suffix_010, ridgeSupport448_suffix_011, ridgeSupport448_suffix_012, ridgeSupport448_suffix_013, ridgeSupport448_suffix_014, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport448_000_mask, ridgeSupport448_001_mask, ridgeSupport448_002_mask, ridgeSupport448_003_mask, ridgeSupport448_004_mask, ridgeSupport448_005_mask, ridgeSupport448_006_mask, ridgeSupport448_007_mask, ridgeSupport448_008_mask, ridgeSupport448_009_mask, ridgeSupport448_010_mask, ridgeSupport448_011_mask, ridgeSupport448_012_mask, ridgeSupport448_013_mask]
    decide +kernel
  · rw [ridgeSupport448_eq]
    simp only [ridgeSupport448_suffix_000, ridgeSupport448_suffix_001, ridgeSupport448_suffix_002, ridgeSupport448_suffix_003, ridgeSupport448_suffix_004, ridgeSupport448_suffix_005, ridgeSupport448_suffix_006, ridgeSupport448_suffix_007, ridgeSupport448_suffix_008, ridgeSupport448_suffix_009, ridgeSupport448_suffix_010, ridgeSupport448_suffix_011, ridgeSupport448_suffix_012, ridgeSupport448_suffix_013, ridgeSupport448_suffix_014, List.all_append, List.all_nil, ridgeSupport448_000_checked, ridgeSupport448_001_checked, ridgeSupport448_002_checked, ridgeSupport448_003_checked, ridgeSupport448_004_checked, ridgeSupport448_005_checked, ridgeSupport448_006_checked, ridgeSupport448_007_checked, ridgeSupport448_008_checked, ridgeSupport448_009_checked, ridgeSupport448_010_checked, ridgeSupport448_011_checked, ridgeSupport448_012_checked, ridgeSupport448_013_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra01
