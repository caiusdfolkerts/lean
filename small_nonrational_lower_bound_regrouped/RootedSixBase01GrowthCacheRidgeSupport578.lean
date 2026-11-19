module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport578Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 578 031 14
cert_ridgeSupport_suffix_decode_2 578 030 14 26 26 031 031 0
cert_ridgeSupport_suffix_decode_2 578 029 14 58 32 031 030 26
cert_ridgeSupport_suffix_decode_2 578 028 14 90 32 031 029 58
cert_ridgeSupport_suffix_decode_2 578 027 14 122 32 031 028 90
cert_ridgeSupport_suffix_decode_2 578 026 14 154 32 031 027 122
cert_ridgeSupport_suffix_decode_2 578 025 14 186 32 031 026 154
cert_ridgeSupport_suffix_decode_2 578 024 14 218 32 031 025 186
cert_ridgeSupport_suffix_decode_2 578 023 14 250 32 031 024 218
cert_ridgeSupport_suffix_decode_2 578 022 14 282 32 031 023 250
cert_ridgeSupport_suffix_decode_2 578 021 14 314 32 031 022 282
cert_ridgeSupport_suffix_decode_2 578 020 14 346 32 031 021 314
cert_ridgeSupport_suffix_decode_2 578 019 14 378 32 031 020 346
cert_ridgeSupport_suffix_decode_2 578 018 14 410 32 031 019 378
cert_ridgeSupport_suffix_decode_2 578 017 14 442 32 031 018 410
cert_ridgeSupport_suffix_decode_2 578 016 14 474 32 031 017 442
cert_ridgeSupport_suffix_decode_2 578 015 14 506 32 031 016 474
cert_ridgeSupport_suffix_decode_2 578 014 14 538 32 031 015 506
cert_ridgeSupport_suffix_decode_2 578 013 14 570 32 031 014 538
cert_ridgeSupport_suffix_decode_2 578 012 14 602 32 031 013 570
cert_ridgeSupport_suffix_decode_2 578 011 14 634 32 031 012 602
cert_ridgeSupport_suffix_decode_2 578 010 14 666 32 031 011 634
cert_ridgeSupport_suffix_decode_2 578 009 14 698 32 031 010 666
cert_ridgeSupport_suffix_decode_2 578 008 14 730 32 031 009 698
cert_ridgeSupport_suffix_decode_2 578 007 14 762 32 031 008 730
cert_ridgeSupport_suffix_decode_2 578 006 14 794 32 031 007 762
cert_ridgeSupport_suffix_decode_2 578 005 14 826 32 031 006 794
cert_ridgeSupport_suffix_decode_2 578 004 14 858 32 031 005 826
cert_ridgeSupport_suffix_decode_2 578 003 14 890 32 031 004 858
cert_ridgeSupport_suffix_decode_2 578 002 14 922 32 031 003 890
cert_ridgeSupport_suffix_decode_2 578 001 14 954 32 031 002 922
cert_ridgeSupport_suffix_decode_2 578 000 14 986 32 031 001 954
cert_ridgeSupport_eq_3 578
theorem ridgeTest_large_578 : ridgeTest 578 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport578_eq]
    simp only [ridgeSupport578_suffix_000, ridgeSupport578_suffix_001, ridgeSupport578_suffix_002, ridgeSupport578_suffix_003, ridgeSupport578_suffix_004, ridgeSupport578_suffix_005, ridgeSupport578_suffix_006, ridgeSupport578_suffix_007, ridgeSupport578_suffix_008, ridgeSupport578_suffix_009, ridgeSupport578_suffix_010, ridgeSupport578_suffix_011, ridgeSupport578_suffix_012, ridgeSupport578_suffix_013, ridgeSupport578_suffix_014, ridgeSupport578_suffix_015, ridgeSupport578_suffix_016, ridgeSupport578_suffix_017, ridgeSupport578_suffix_018, ridgeSupport578_suffix_019, ridgeSupport578_suffix_020, ridgeSupport578_suffix_021, ridgeSupport578_suffix_022, ridgeSupport578_suffix_023, ridgeSupport578_suffix_024, ridgeSupport578_suffix_025, ridgeSupport578_suffix_026, ridgeSupport578_suffix_027, ridgeSupport578_suffix_028, ridgeSupport578_suffix_029, ridgeSupport578_suffix_030, ridgeSupport578_suffix_031, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport578_000_mask, ridgeSupport578_001_mask, ridgeSupport578_002_mask, ridgeSupport578_003_mask, ridgeSupport578_004_mask, ridgeSupport578_005_mask, ridgeSupport578_006_mask, ridgeSupport578_007_mask, ridgeSupport578_008_mask, ridgeSupport578_009_mask, ridgeSupport578_010_mask, ridgeSupport578_011_mask, ridgeSupport578_012_mask, ridgeSupport578_013_mask, ridgeSupport578_014_mask, ridgeSupport578_015_mask, ridgeSupport578_016_mask, ridgeSupport578_017_mask, ridgeSupport578_018_mask, ridgeSupport578_019_mask, ridgeSupport578_020_mask, ridgeSupport578_021_mask, ridgeSupport578_022_mask, ridgeSupport578_023_mask, ridgeSupport578_024_mask, ridgeSupport578_025_mask, ridgeSupport578_026_mask, ridgeSupport578_027_mask, ridgeSupport578_028_mask, ridgeSupport578_029_mask, ridgeSupport578_030_mask]
    decide +kernel
  · rw [ridgeSupport578_eq]
    simp only [ridgeSupport578_suffix_000, ridgeSupport578_suffix_001, ridgeSupport578_suffix_002, ridgeSupport578_suffix_003, ridgeSupport578_suffix_004, ridgeSupport578_suffix_005, ridgeSupport578_suffix_006, ridgeSupport578_suffix_007, ridgeSupport578_suffix_008, ridgeSupport578_suffix_009, ridgeSupport578_suffix_010, ridgeSupport578_suffix_011, ridgeSupport578_suffix_012, ridgeSupport578_suffix_013, ridgeSupport578_suffix_014, ridgeSupport578_suffix_015, ridgeSupport578_suffix_016, ridgeSupport578_suffix_017, ridgeSupport578_suffix_018, ridgeSupport578_suffix_019, ridgeSupport578_suffix_020, ridgeSupport578_suffix_021, ridgeSupport578_suffix_022, ridgeSupport578_suffix_023, ridgeSupport578_suffix_024, ridgeSupport578_suffix_025, ridgeSupport578_suffix_026, ridgeSupport578_suffix_027, ridgeSupport578_suffix_028, ridgeSupport578_suffix_029, ridgeSupport578_suffix_030, ridgeSupport578_suffix_031, List.all_append, List.all_nil, ridgeSupport578_000_checked, ridgeSupport578_001_checked, ridgeSupport578_002_checked, ridgeSupport578_003_checked, ridgeSupport578_004_checked, ridgeSupport578_005_checked, ridgeSupport578_006_checked, ridgeSupport578_007_checked, ridgeSupport578_008_checked, ridgeSupport578_009_checked, ridgeSupport578_010_checked, ridgeSupport578_011_checked, ridgeSupport578_012_checked, ridgeSupport578_013_checked, ridgeSupport578_014_checked, ridgeSupport578_015_checked, ridgeSupport578_016_checked, ridgeSupport578_017_checked, ridgeSupport578_018_checked, ridgeSupport578_019_checked, ridgeSupport578_020_checked, ridgeSupport578_021_checked, ridgeSupport578_022_checked, ridgeSupport578_023_checked, ridgeSupport578_024_checked, ridgeSupport578_025_checked, ridgeSupport578_026_checked, ridgeSupport578_027_checked, ridgeSupport578_028_checked, ridgeSupport578_029_checked, ridgeSupport578_030_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
