module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra01GrowthCacheRidgeSupport704Part000
public import RootedSixExtra01GrowthCacheRidgeSupport704Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 704 014 12
cert_ridgeSupport_suffix_decode_4 704 013 12 29 29 014 014 0
cert_ridgeSupport_suffix_decode_4 704 012 12 61 32 014 013 29
cert_ridgeSupport_suffix_decode_4 704 011 12 93 32 014 012 61
cert_ridgeSupport_suffix_decode_4 704 010 12 125 32 014 011 93
cert_ridgeSupport_suffix_decode_4 704 009 12 157 32 014 010 125
cert_ridgeSupport_suffix_decode_4 704 008 12 189 32 014 009 157
cert_ridgeSupport_suffix_decode_4 704 007 12 221 32 014 008 189
cert_ridgeSupport_suffix_decode_4 704 006 12 253 32 014 007 221
cert_ridgeSupport_suffix_decode_4 704 005 12 285 32 014 006 253
cert_ridgeSupport_suffix_decode_4 704 004 12 317 32 014 005 285
cert_ridgeSupport_suffix_decode_4 704 003 12 349 32 014 004 317
cert_ridgeSupport_suffix_decode_4 704 002 12 381 32 014 003 349
cert_ridgeSupport_suffix_decode_4 704 001 12 413 32 014 002 381
cert_ridgeSupport_suffix_decode_4 704 000 12 445 32 014 001 413
cert_ridgeSupport_eq_4 704
theorem ridgeTest_large_704 : ridgeTest 704 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport704_eq]
    simp only [ridgeSupport704_suffix_000, ridgeSupport704_suffix_001, ridgeSupport704_suffix_002, ridgeSupport704_suffix_003, ridgeSupport704_suffix_004, ridgeSupport704_suffix_005, ridgeSupport704_suffix_006, ridgeSupport704_suffix_007, ridgeSupport704_suffix_008, ridgeSupport704_suffix_009, ridgeSupport704_suffix_010, ridgeSupport704_suffix_011, ridgeSupport704_suffix_012, ridgeSupport704_suffix_013, ridgeSupport704_suffix_014, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport704_000_mask, ridgeSupport704_001_mask, ridgeSupport704_002_mask, ridgeSupport704_003_mask, ridgeSupport704_004_mask, ridgeSupport704_005_mask, ridgeSupport704_006_mask, ridgeSupport704_007_mask, ridgeSupport704_008_mask, ridgeSupport704_009_mask, ridgeSupport704_010_mask, ridgeSupport704_011_mask, ridgeSupport704_012_mask, ridgeSupport704_013_mask]
    decide +kernel
  · rw [ridgeSupport704_eq]
    simp only [ridgeSupport704_suffix_000, ridgeSupport704_suffix_001, ridgeSupport704_suffix_002, ridgeSupport704_suffix_003, ridgeSupport704_suffix_004, ridgeSupport704_suffix_005, ridgeSupport704_suffix_006, ridgeSupport704_suffix_007, ridgeSupport704_suffix_008, ridgeSupport704_suffix_009, ridgeSupport704_suffix_010, ridgeSupport704_suffix_011, ridgeSupport704_suffix_012, ridgeSupport704_suffix_013, ridgeSupport704_suffix_014, List.all_append, List.all_nil, ridgeSupport704_000_checked, ridgeSupport704_001_checked, ridgeSupport704_002_checked, ridgeSupport704_003_checked, ridgeSupport704_004_checked, ridgeSupport704_005_checked, ridgeSupport704_006_checked, ridgeSupport704_007_checked, ridgeSupport704_008_checked, ridgeSupport704_009_checked, ridgeSupport704_010_checked, ridgeSupport704_011_checked, ridgeSupport704_012_checked, ridgeSupport704_013_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra01
