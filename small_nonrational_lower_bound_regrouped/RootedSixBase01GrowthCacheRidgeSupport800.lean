module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase01GrowthCacheRidgeSupport800PartGrouped000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 800 023 14
cert_ridgeSupport_suffix_decode_2 800 022 14 15 15 023 023 0
cert_ridgeSupport_suffix_decode_2 800 021 14 47 32 023 022 15
cert_ridgeSupport_suffix_decode_2 800 020 14 79 32 023 021 47
cert_ridgeSupport_suffix_decode_2 800 019 14 111 32 023 020 79
cert_ridgeSupport_suffix_decode_2 800 018 14 143 32 023 019 111
cert_ridgeSupport_suffix_decode_2 800 017 14 175 32 023 018 143
cert_ridgeSupport_suffix_decode_2 800 016 14 207 32 023 017 175
cert_ridgeSupport_suffix_decode_2 800 015 14 239 32 023 016 207
cert_ridgeSupport_suffix_decode_2 800 014 14 271 32 023 015 239
cert_ridgeSupport_suffix_decode_2 800 013 14 303 32 023 014 271
cert_ridgeSupport_suffix_decode_2 800 012 14 335 32 023 013 303
cert_ridgeSupport_suffix_decode_2 800 011 14 367 32 023 012 335
cert_ridgeSupport_suffix_decode_2 800 010 14 399 32 023 011 367
cert_ridgeSupport_suffix_decode_2 800 009 14 431 32 023 010 399
cert_ridgeSupport_suffix_decode_2 800 008 14 463 32 023 009 431
cert_ridgeSupport_suffix_decode_2 800 007 14 495 32 023 008 463
cert_ridgeSupport_suffix_decode_2 800 006 14 527 32 023 007 495
cert_ridgeSupport_suffix_decode_2 800 005 14 559 32 023 006 527
cert_ridgeSupport_suffix_decode_2 800 004 14 591 32 023 005 559
cert_ridgeSupport_suffix_decode_2 800 003 14 623 32 023 004 591
cert_ridgeSupport_suffix_decode_2 800 002 14 655 32 023 003 623
cert_ridgeSupport_suffix_decode_2 800 001 14 687 32 023 002 655
cert_ridgeSupport_suffix_decode_2 800 000 14 719 32 023 001 687
cert_ridgeSupport_eq_3 800
theorem ridgeTest_large_800 : ridgeTest 800 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport800_eq]
    simp only [ridgeSupport800_suffix_000, ridgeSupport800_suffix_001, ridgeSupport800_suffix_002, ridgeSupport800_suffix_003, ridgeSupport800_suffix_004, ridgeSupport800_suffix_005, ridgeSupport800_suffix_006, ridgeSupport800_suffix_007, ridgeSupport800_suffix_008, ridgeSupport800_suffix_009, ridgeSupport800_suffix_010, ridgeSupport800_suffix_011, ridgeSupport800_suffix_012, ridgeSupport800_suffix_013, ridgeSupport800_suffix_014, ridgeSupport800_suffix_015, ridgeSupport800_suffix_016, ridgeSupport800_suffix_017, ridgeSupport800_suffix_018, ridgeSupport800_suffix_019, ridgeSupport800_suffix_020, ridgeSupport800_suffix_021, ridgeSupport800_suffix_022, ridgeSupport800_suffix_023, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport800_000_mask, ridgeSupport800_001_mask, ridgeSupport800_002_mask, ridgeSupport800_003_mask, ridgeSupport800_004_mask, ridgeSupport800_005_mask, ridgeSupport800_006_mask, ridgeSupport800_007_mask, ridgeSupport800_008_mask, ridgeSupport800_009_mask, ridgeSupport800_010_mask, ridgeSupport800_011_mask, ridgeSupport800_012_mask, ridgeSupport800_013_mask, ridgeSupport800_014_mask, ridgeSupport800_015_mask, ridgeSupport800_016_mask, ridgeSupport800_017_mask, ridgeSupport800_018_mask, ridgeSupport800_019_mask, ridgeSupport800_020_mask, ridgeSupport800_021_mask, ridgeSupport800_022_mask]
    decide +kernel
  · rw [ridgeSupport800_eq]
    simp only [ridgeSupport800_suffix_000, ridgeSupport800_suffix_001, ridgeSupport800_suffix_002, ridgeSupport800_suffix_003, ridgeSupport800_suffix_004, ridgeSupport800_suffix_005, ridgeSupport800_suffix_006, ridgeSupport800_suffix_007, ridgeSupport800_suffix_008, ridgeSupport800_suffix_009, ridgeSupport800_suffix_010, ridgeSupport800_suffix_011, ridgeSupport800_suffix_012, ridgeSupport800_suffix_013, ridgeSupport800_suffix_014, ridgeSupport800_suffix_015, ridgeSupport800_suffix_016, ridgeSupport800_suffix_017, ridgeSupport800_suffix_018, ridgeSupport800_suffix_019, ridgeSupport800_suffix_020, ridgeSupport800_suffix_021, ridgeSupport800_suffix_022, ridgeSupport800_suffix_023, List.all_append, List.all_nil, ridgeSupport800_000_checked, ridgeSupport800_001_checked, ridgeSupport800_002_checked, ridgeSupport800_003_checked, ridgeSupport800_004_checked, ridgeSupport800_005_checked, ridgeSupport800_006_checked, ridgeSupport800_007_checked, ridgeSupport800_008_checked, ridgeSupport800_009_checked, ridgeSupport800_010_checked, ridgeSupport800_011_checked, ridgeSupport800_012_checked, ridgeSupport800_013_checked, ridgeSupport800_014_checked, ridgeSupport800_015_checked, ridgeSupport800_016_checked, ridgeSupport800_017_checked, ridgeSupport800_018_checked, ridgeSupport800_019_checked, ridgeSupport800_020_checked, ridgeSupport800_021_checked, ridgeSupport800_022_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
