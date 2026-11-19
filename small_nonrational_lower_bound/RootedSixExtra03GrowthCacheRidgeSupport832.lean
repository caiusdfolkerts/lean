module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra03GrowthCacheRidgeSupport832Part000
public import RootedSixExtra03GrowthCacheRidgeSupport832Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 832 014 12
cert_ridgeSupport_suffix_decode_4 832 013 12 29 29 014 014 0
cert_ridgeSupport_suffix_decode_4 832 012 12 61 32 014 013 29
cert_ridgeSupport_suffix_decode_4 832 011 12 93 32 014 012 61
cert_ridgeSupport_suffix_decode_4 832 010 12 125 32 014 011 93
cert_ridgeSupport_suffix_decode_4 832 009 12 157 32 014 010 125
cert_ridgeSupport_suffix_decode_4 832 008 12 189 32 014 009 157
cert_ridgeSupport_suffix_decode_4 832 007 12 221 32 014 008 189
cert_ridgeSupport_suffix_decode_4 832 006 12 253 32 014 007 221
cert_ridgeSupport_suffix_decode_4 832 005 12 285 32 014 006 253
cert_ridgeSupport_suffix_decode_4 832 004 12 317 32 014 005 285
cert_ridgeSupport_suffix_decode_4 832 003 12 349 32 014 004 317
cert_ridgeSupport_suffix_decode_4 832 002 12 381 32 014 003 349
cert_ridgeSupport_suffix_decode_4 832 001 12 413 32 014 002 381
cert_ridgeSupport_suffix_decode_4 832 000 12 445 32 014 001 413
cert_ridgeSupport_eq_4 832
theorem ridgeTest_large_832 : ridgeTest 832 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport832_eq]
    simp only [ridgeSupport832_suffix_000, ridgeSupport832_suffix_001, ridgeSupport832_suffix_002, ridgeSupport832_suffix_003, ridgeSupport832_suffix_004, ridgeSupport832_suffix_005, ridgeSupport832_suffix_006, ridgeSupport832_suffix_007, ridgeSupport832_suffix_008, ridgeSupport832_suffix_009, ridgeSupport832_suffix_010, ridgeSupport832_suffix_011, ridgeSupport832_suffix_012, ridgeSupport832_suffix_013, ridgeSupport832_suffix_014, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport832_000_mask, ridgeSupport832_001_mask, ridgeSupport832_002_mask, ridgeSupport832_003_mask, ridgeSupport832_004_mask, ridgeSupport832_005_mask, ridgeSupport832_006_mask, ridgeSupport832_007_mask, ridgeSupport832_008_mask, ridgeSupport832_009_mask, ridgeSupport832_010_mask, ridgeSupport832_011_mask, ridgeSupport832_012_mask, ridgeSupport832_013_mask]
    decide +kernel
  · rw [ridgeSupport832_eq]
    simp only [ridgeSupport832_suffix_000, ridgeSupport832_suffix_001, ridgeSupport832_suffix_002, ridgeSupport832_suffix_003, ridgeSupport832_suffix_004, ridgeSupport832_suffix_005, ridgeSupport832_suffix_006, ridgeSupport832_suffix_007, ridgeSupport832_suffix_008, ridgeSupport832_suffix_009, ridgeSupport832_suffix_010, ridgeSupport832_suffix_011, ridgeSupport832_suffix_012, ridgeSupport832_suffix_013, ridgeSupport832_suffix_014, List.all_append, List.all_nil, ridgeSupport832_000_checked, ridgeSupport832_001_checked, ridgeSupport832_002_checked, ridgeSupport832_003_checked, ridgeSupport832_004_checked, ridgeSupport832_005_checked, ridgeSupport832_006_checked, ridgeSupport832_007_checked, ridgeSupport832_008_checked, ridgeSupport832_009_checked, ridgeSupport832_010_checked, ridgeSupport832_011_checked, ridgeSupport832_012_checked, ridgeSupport832_013_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra03
