module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase01GrowthCacheRidgeSupport784PartGrouped000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 784 023 14
cert_ridgeSupport_suffix_decode_2 784 022 14 15 15 023 023 0
cert_ridgeSupport_suffix_decode_2 784 021 14 47 32 023 022 15
cert_ridgeSupport_suffix_decode_2 784 020 14 79 32 023 021 47
cert_ridgeSupport_suffix_decode_2 784 019 14 111 32 023 020 79
cert_ridgeSupport_suffix_decode_2 784 018 14 143 32 023 019 111
cert_ridgeSupport_suffix_decode_2 784 017 14 175 32 023 018 143
cert_ridgeSupport_suffix_decode_2 784 016 14 207 32 023 017 175
cert_ridgeSupport_suffix_decode_2 784 015 14 239 32 023 016 207
cert_ridgeSupport_suffix_decode_2 784 014 14 271 32 023 015 239
cert_ridgeSupport_suffix_decode_2 784 013 14 303 32 023 014 271
cert_ridgeSupport_suffix_decode_2 784 012 14 335 32 023 013 303
cert_ridgeSupport_suffix_decode_2 784 011 14 367 32 023 012 335
cert_ridgeSupport_suffix_decode_2 784 010 14 399 32 023 011 367
cert_ridgeSupport_suffix_decode_2 784 009 14 431 32 023 010 399
cert_ridgeSupport_suffix_decode_2 784 008 14 463 32 023 009 431
cert_ridgeSupport_suffix_decode_2 784 007 14 495 32 023 008 463
cert_ridgeSupport_suffix_decode_2 784 006 14 527 32 023 007 495
cert_ridgeSupport_suffix_decode_2 784 005 14 559 32 023 006 527
cert_ridgeSupport_suffix_decode_2 784 004 14 591 32 023 005 559
cert_ridgeSupport_suffix_decode_2 784 003 14 623 32 023 004 591
cert_ridgeSupport_suffix_decode_2 784 002 14 655 32 023 003 623
cert_ridgeSupport_suffix_decode_2 784 001 14 687 32 023 002 655
cert_ridgeSupport_suffix_decode_2 784 000 14 719 32 023 001 687
cert_ridgeSupport_eq_3 784
theorem ridgeTest_large_784 : ridgeTest 784 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport784_eq]
    simp only [ridgeSupport784_suffix_000, ridgeSupport784_suffix_001, ridgeSupport784_suffix_002, ridgeSupport784_suffix_003, ridgeSupport784_suffix_004, ridgeSupport784_suffix_005, ridgeSupport784_suffix_006, ridgeSupport784_suffix_007, ridgeSupport784_suffix_008, ridgeSupport784_suffix_009, ridgeSupport784_suffix_010, ridgeSupport784_suffix_011, ridgeSupport784_suffix_012, ridgeSupport784_suffix_013, ridgeSupport784_suffix_014, ridgeSupport784_suffix_015, ridgeSupport784_suffix_016, ridgeSupport784_suffix_017, ridgeSupport784_suffix_018, ridgeSupport784_suffix_019, ridgeSupport784_suffix_020, ridgeSupport784_suffix_021, ridgeSupport784_suffix_022, ridgeSupport784_suffix_023, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport784_000_mask, ridgeSupport784_001_mask, ridgeSupport784_002_mask, ridgeSupport784_003_mask, ridgeSupport784_004_mask, ridgeSupport784_005_mask, ridgeSupport784_006_mask, ridgeSupport784_007_mask, ridgeSupport784_008_mask, ridgeSupport784_009_mask, ridgeSupport784_010_mask, ridgeSupport784_011_mask, ridgeSupport784_012_mask, ridgeSupport784_013_mask, ridgeSupport784_014_mask, ridgeSupport784_015_mask, ridgeSupport784_016_mask, ridgeSupport784_017_mask, ridgeSupport784_018_mask, ridgeSupport784_019_mask, ridgeSupport784_020_mask, ridgeSupport784_021_mask, ridgeSupport784_022_mask]
    decide +kernel
  · rw [ridgeSupport784_eq]
    simp only [ridgeSupport784_suffix_000, ridgeSupport784_suffix_001, ridgeSupport784_suffix_002, ridgeSupport784_suffix_003, ridgeSupport784_suffix_004, ridgeSupport784_suffix_005, ridgeSupport784_suffix_006, ridgeSupport784_suffix_007, ridgeSupport784_suffix_008, ridgeSupport784_suffix_009, ridgeSupport784_suffix_010, ridgeSupport784_suffix_011, ridgeSupport784_suffix_012, ridgeSupport784_suffix_013, ridgeSupport784_suffix_014, ridgeSupport784_suffix_015, ridgeSupport784_suffix_016, ridgeSupport784_suffix_017, ridgeSupport784_suffix_018, ridgeSupport784_suffix_019, ridgeSupport784_suffix_020, ridgeSupport784_suffix_021, ridgeSupport784_suffix_022, ridgeSupport784_suffix_023, List.all_append, List.all_nil, ridgeSupport784_000_checked, ridgeSupport784_001_checked, ridgeSupport784_002_checked, ridgeSupport784_003_checked, ridgeSupport784_004_checked, ridgeSupport784_005_checked, ridgeSupport784_006_checked, ridgeSupport784_007_checked, ridgeSupport784_008_checked, ridgeSupport784_009_checked, ridgeSupport784_010_checked, ridgeSupport784_011_checked, ridgeSupport784_012_checked, ridgeSupport784_013_checked, ridgeSupport784_014_checked, ridgeSupport784_015_checked, ridgeSupport784_016_checked, ridgeSupport784_017_checked, ridgeSupport784_018_checked, ridgeSupport784_019_checked, ridgeSupport784_020_checked, ridgeSupport784_021_checked, ridgeSupport784_022_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
