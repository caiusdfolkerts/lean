module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra03GrowthCacheRidgeSupport896Part000
public import RootedSixExtra03GrowthCacheRidgeSupport896Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 896 014 12
cert_ridgeSupport_suffix_decode_4 896 013 12 29 29 014 014 0
cert_ridgeSupport_suffix_decode_4 896 012 12 61 32 014 013 29
cert_ridgeSupport_suffix_decode_4 896 011 12 93 32 014 012 61
cert_ridgeSupport_suffix_decode_4 896 010 12 125 32 014 011 93
cert_ridgeSupport_suffix_decode_4 896 009 12 157 32 014 010 125
cert_ridgeSupport_suffix_decode_4 896 008 12 189 32 014 009 157
cert_ridgeSupport_suffix_decode_4 896 007 12 221 32 014 008 189
cert_ridgeSupport_suffix_decode_4 896 006 12 253 32 014 007 221
cert_ridgeSupport_suffix_decode_4 896 005 12 285 32 014 006 253
cert_ridgeSupport_suffix_decode_4 896 004 12 317 32 014 005 285
cert_ridgeSupport_suffix_decode_4 896 003 12 349 32 014 004 317
cert_ridgeSupport_suffix_decode_4 896 002 12 381 32 014 003 349
cert_ridgeSupport_suffix_decode_4 896 001 12 413 32 014 002 381
cert_ridgeSupport_suffix_decode_4 896 000 12 445 32 014 001 413
cert_ridgeSupport_eq_4 896
theorem ridgeTest_large_896 : ridgeTest 896 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport896_eq]
    simp only [ridgeSupport896_suffix_000, ridgeSupport896_suffix_001, ridgeSupport896_suffix_002, ridgeSupport896_suffix_003, ridgeSupport896_suffix_004, ridgeSupport896_suffix_005, ridgeSupport896_suffix_006, ridgeSupport896_suffix_007, ridgeSupport896_suffix_008, ridgeSupport896_suffix_009, ridgeSupport896_suffix_010, ridgeSupport896_suffix_011, ridgeSupport896_suffix_012, ridgeSupport896_suffix_013, ridgeSupport896_suffix_014, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport896_000_mask, ridgeSupport896_001_mask, ridgeSupport896_002_mask, ridgeSupport896_003_mask, ridgeSupport896_004_mask, ridgeSupport896_005_mask, ridgeSupport896_006_mask, ridgeSupport896_007_mask, ridgeSupport896_008_mask, ridgeSupport896_009_mask, ridgeSupport896_010_mask, ridgeSupport896_011_mask, ridgeSupport896_012_mask, ridgeSupport896_013_mask]
    decide +kernel
  · rw [ridgeSupport896_eq]
    simp only [ridgeSupport896_suffix_000, ridgeSupport896_suffix_001, ridgeSupport896_suffix_002, ridgeSupport896_suffix_003, ridgeSupport896_suffix_004, ridgeSupport896_suffix_005, ridgeSupport896_suffix_006, ridgeSupport896_suffix_007, ridgeSupport896_suffix_008, ridgeSupport896_suffix_009, ridgeSupport896_suffix_010, ridgeSupport896_suffix_011, ridgeSupport896_suffix_012, ridgeSupport896_suffix_013, ridgeSupport896_suffix_014, List.all_append, List.all_nil, ridgeSupport896_000_checked, ridgeSupport896_001_checked, ridgeSupport896_002_checked, ridgeSupport896_003_checked, ridgeSupport896_004_checked, ridgeSupport896_005_checked, ridgeSupport896_006_checked, ridgeSupport896_007_checked, ridgeSupport896_008_checked, ridgeSupport896_009_checked, ridgeSupport896_010_checked, ridgeSupport896_011_checked, ridgeSupport896_012_checked, ridgeSupport896_013_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra03
