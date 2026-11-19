module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase01GrowthCacheRidgeSupport352PartGrouped000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 352 023 14
cert_ridgeSupport_suffix_decode_2 352 022 14 15 15 023 023 0
cert_ridgeSupport_suffix_decode_2 352 021 14 47 32 023 022 15
cert_ridgeSupport_suffix_decode_2 352 020 14 79 32 023 021 47
cert_ridgeSupport_suffix_decode_2 352 019 14 111 32 023 020 79
cert_ridgeSupport_suffix_decode_2 352 018 14 143 32 023 019 111
cert_ridgeSupport_suffix_decode_2 352 017 14 175 32 023 018 143
cert_ridgeSupport_suffix_decode_2 352 016 14 207 32 023 017 175
cert_ridgeSupport_suffix_decode_2 352 015 14 239 32 023 016 207
cert_ridgeSupport_suffix_decode_2 352 014 14 271 32 023 015 239
cert_ridgeSupport_suffix_decode_2 352 013 14 303 32 023 014 271
cert_ridgeSupport_suffix_decode_2 352 012 14 335 32 023 013 303
cert_ridgeSupport_suffix_decode_2 352 011 14 367 32 023 012 335
cert_ridgeSupport_suffix_decode_2 352 010 14 399 32 023 011 367
cert_ridgeSupport_suffix_decode_2 352 009 14 431 32 023 010 399
cert_ridgeSupport_suffix_decode_2 352 008 14 463 32 023 009 431
cert_ridgeSupport_suffix_decode_2 352 007 14 495 32 023 008 463
cert_ridgeSupport_suffix_decode_2 352 006 14 527 32 023 007 495
cert_ridgeSupport_suffix_decode_2 352 005 14 559 32 023 006 527
cert_ridgeSupport_suffix_decode_2 352 004 14 591 32 023 005 559
cert_ridgeSupport_suffix_decode_2 352 003 14 623 32 023 004 591
cert_ridgeSupport_suffix_decode_2 352 002 14 655 32 023 003 623
cert_ridgeSupport_suffix_decode_2 352 001 14 687 32 023 002 655
cert_ridgeSupport_suffix_decode_2 352 000 14 719 32 023 001 687
cert_ridgeSupport_eq_3 352
theorem ridgeTest_large_352 : ridgeTest 352 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport352_eq]
    simp only [ridgeSupport352_suffix_000, ridgeSupport352_suffix_001, ridgeSupport352_suffix_002, ridgeSupport352_suffix_003, ridgeSupport352_suffix_004, ridgeSupport352_suffix_005, ridgeSupport352_suffix_006, ridgeSupport352_suffix_007, ridgeSupport352_suffix_008, ridgeSupport352_suffix_009, ridgeSupport352_suffix_010, ridgeSupport352_suffix_011, ridgeSupport352_suffix_012, ridgeSupport352_suffix_013, ridgeSupport352_suffix_014, ridgeSupport352_suffix_015, ridgeSupport352_suffix_016, ridgeSupport352_suffix_017, ridgeSupport352_suffix_018, ridgeSupport352_suffix_019, ridgeSupport352_suffix_020, ridgeSupport352_suffix_021, ridgeSupport352_suffix_022, ridgeSupport352_suffix_023, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport352_000_mask, ridgeSupport352_001_mask, ridgeSupport352_002_mask, ridgeSupport352_003_mask, ridgeSupport352_004_mask, ridgeSupport352_005_mask, ridgeSupport352_006_mask, ridgeSupport352_007_mask, ridgeSupport352_008_mask, ridgeSupport352_009_mask, ridgeSupport352_010_mask, ridgeSupport352_011_mask, ridgeSupport352_012_mask, ridgeSupport352_013_mask, ridgeSupport352_014_mask, ridgeSupport352_015_mask, ridgeSupport352_016_mask, ridgeSupport352_017_mask, ridgeSupport352_018_mask, ridgeSupport352_019_mask, ridgeSupport352_020_mask, ridgeSupport352_021_mask, ridgeSupport352_022_mask]
    decide +kernel
  · rw [ridgeSupport352_eq]
    simp only [ridgeSupport352_suffix_000, ridgeSupport352_suffix_001, ridgeSupport352_suffix_002, ridgeSupport352_suffix_003, ridgeSupport352_suffix_004, ridgeSupport352_suffix_005, ridgeSupport352_suffix_006, ridgeSupport352_suffix_007, ridgeSupport352_suffix_008, ridgeSupport352_suffix_009, ridgeSupport352_suffix_010, ridgeSupport352_suffix_011, ridgeSupport352_suffix_012, ridgeSupport352_suffix_013, ridgeSupport352_suffix_014, ridgeSupport352_suffix_015, ridgeSupport352_suffix_016, ridgeSupport352_suffix_017, ridgeSupport352_suffix_018, ridgeSupport352_suffix_019, ridgeSupport352_suffix_020, ridgeSupport352_suffix_021, ridgeSupport352_suffix_022, ridgeSupport352_suffix_023, List.all_append, List.all_nil, ridgeSupport352_000_checked, ridgeSupport352_001_checked, ridgeSupport352_002_checked, ridgeSupport352_003_checked, ridgeSupport352_004_checked, ridgeSupport352_005_checked, ridgeSupport352_006_checked, ridgeSupport352_007_checked, ridgeSupport352_008_checked, ridgeSupport352_009_checked, ridgeSupport352_010_checked, ridgeSupport352_011_checked, ridgeSupport352_012_checked, ridgeSupport352_013_checked, ridgeSupport352_014_checked, ridgeSupport352_015_checked, ridgeSupport352_016_checked, ridgeSupport352_017_checked, ridgeSupport352_018_checked, ridgeSupport352_019_checked, ridgeSupport352_020_checked, ridgeSupport352_021_checked, ridgeSupport352_022_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
