module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport322Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 322 031 14
cert_ridgeSupport_suffix_decode_2 322 030 14 26 26 031 031 0
cert_ridgeSupport_suffix_decode_2 322 029 14 58 32 031 030 26
cert_ridgeSupport_suffix_decode_2 322 028 14 90 32 031 029 58
cert_ridgeSupport_suffix_decode_2 322 027 14 122 32 031 028 90
cert_ridgeSupport_suffix_decode_2 322 026 14 154 32 031 027 122
cert_ridgeSupport_suffix_decode_2 322 025 14 186 32 031 026 154
cert_ridgeSupport_suffix_decode_2 322 024 14 218 32 031 025 186
cert_ridgeSupport_suffix_decode_2 322 023 14 250 32 031 024 218
cert_ridgeSupport_suffix_decode_2 322 022 14 282 32 031 023 250
cert_ridgeSupport_suffix_decode_2 322 021 14 314 32 031 022 282
cert_ridgeSupport_suffix_decode_2 322 020 14 346 32 031 021 314
cert_ridgeSupport_suffix_decode_2 322 019 14 378 32 031 020 346
cert_ridgeSupport_suffix_decode_2 322 018 14 410 32 031 019 378
cert_ridgeSupport_suffix_decode_2 322 017 14 442 32 031 018 410
cert_ridgeSupport_suffix_decode_2 322 016 14 474 32 031 017 442
cert_ridgeSupport_suffix_decode_2 322 015 14 506 32 031 016 474
cert_ridgeSupport_suffix_decode_2 322 014 14 538 32 031 015 506
cert_ridgeSupport_suffix_decode_2 322 013 14 570 32 031 014 538
cert_ridgeSupport_suffix_decode_2 322 012 14 602 32 031 013 570
cert_ridgeSupport_suffix_decode_2 322 011 14 634 32 031 012 602
cert_ridgeSupport_suffix_decode_2 322 010 14 666 32 031 011 634
cert_ridgeSupport_suffix_decode_2 322 009 14 698 32 031 010 666
cert_ridgeSupport_suffix_decode_2 322 008 14 730 32 031 009 698
cert_ridgeSupport_suffix_decode_2 322 007 14 762 32 031 008 730
cert_ridgeSupport_suffix_decode_2 322 006 14 794 32 031 007 762
cert_ridgeSupport_suffix_decode_2 322 005 14 826 32 031 006 794
cert_ridgeSupport_suffix_decode_2 322 004 14 858 32 031 005 826
cert_ridgeSupport_suffix_decode_2 322 003 14 890 32 031 004 858
cert_ridgeSupport_suffix_decode_2 322 002 14 922 32 031 003 890
cert_ridgeSupport_suffix_decode_2 322 001 14 954 32 031 002 922
cert_ridgeSupport_suffix_decode_2 322 000 14 986 32 031 001 954
cert_ridgeSupport_eq_3 322
theorem ridgeTest_large_322 : ridgeTest 322 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport322_eq]
    simp only [ridgeSupport322_suffix_000, ridgeSupport322_suffix_001, ridgeSupport322_suffix_002, ridgeSupport322_suffix_003, ridgeSupport322_suffix_004, ridgeSupport322_suffix_005, ridgeSupport322_suffix_006, ridgeSupport322_suffix_007, ridgeSupport322_suffix_008, ridgeSupport322_suffix_009, ridgeSupport322_suffix_010, ridgeSupport322_suffix_011, ridgeSupport322_suffix_012, ridgeSupport322_suffix_013, ridgeSupport322_suffix_014, ridgeSupport322_suffix_015, ridgeSupport322_suffix_016, ridgeSupport322_suffix_017, ridgeSupport322_suffix_018, ridgeSupport322_suffix_019, ridgeSupport322_suffix_020, ridgeSupport322_suffix_021, ridgeSupport322_suffix_022, ridgeSupport322_suffix_023, ridgeSupport322_suffix_024, ridgeSupport322_suffix_025, ridgeSupport322_suffix_026, ridgeSupport322_suffix_027, ridgeSupport322_suffix_028, ridgeSupport322_suffix_029, ridgeSupport322_suffix_030, ridgeSupport322_suffix_031, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport322_000_mask, ridgeSupport322_001_mask, ridgeSupport322_002_mask, ridgeSupport322_003_mask, ridgeSupport322_004_mask, ridgeSupport322_005_mask, ridgeSupport322_006_mask, ridgeSupport322_007_mask, ridgeSupport322_008_mask, ridgeSupport322_009_mask, ridgeSupport322_010_mask, ridgeSupport322_011_mask, ridgeSupport322_012_mask, ridgeSupport322_013_mask, ridgeSupport322_014_mask, ridgeSupport322_015_mask, ridgeSupport322_016_mask, ridgeSupport322_017_mask, ridgeSupport322_018_mask, ridgeSupport322_019_mask, ridgeSupport322_020_mask, ridgeSupport322_021_mask, ridgeSupport322_022_mask, ridgeSupport322_023_mask, ridgeSupport322_024_mask, ridgeSupport322_025_mask, ridgeSupport322_026_mask, ridgeSupport322_027_mask, ridgeSupport322_028_mask, ridgeSupport322_029_mask, ridgeSupport322_030_mask]
    decide +kernel
  · rw [ridgeSupport322_eq]
    simp only [ridgeSupport322_suffix_000, ridgeSupport322_suffix_001, ridgeSupport322_suffix_002, ridgeSupport322_suffix_003, ridgeSupport322_suffix_004, ridgeSupport322_suffix_005, ridgeSupport322_suffix_006, ridgeSupport322_suffix_007, ridgeSupport322_suffix_008, ridgeSupport322_suffix_009, ridgeSupport322_suffix_010, ridgeSupport322_suffix_011, ridgeSupport322_suffix_012, ridgeSupport322_suffix_013, ridgeSupport322_suffix_014, ridgeSupport322_suffix_015, ridgeSupport322_suffix_016, ridgeSupport322_suffix_017, ridgeSupport322_suffix_018, ridgeSupport322_suffix_019, ridgeSupport322_suffix_020, ridgeSupport322_suffix_021, ridgeSupport322_suffix_022, ridgeSupport322_suffix_023, ridgeSupport322_suffix_024, ridgeSupport322_suffix_025, ridgeSupport322_suffix_026, ridgeSupport322_suffix_027, ridgeSupport322_suffix_028, ridgeSupport322_suffix_029, ridgeSupport322_suffix_030, ridgeSupport322_suffix_031, List.all_append, List.all_nil, ridgeSupport322_000_checked, ridgeSupport322_001_checked, ridgeSupport322_002_checked, ridgeSupport322_003_checked, ridgeSupport322_004_checked, ridgeSupport322_005_checked, ridgeSupport322_006_checked, ridgeSupport322_007_checked, ridgeSupport322_008_checked, ridgeSupport322_009_checked, ridgeSupport322_010_checked, ridgeSupport322_011_checked, ridgeSupport322_012_checked, ridgeSupport322_013_checked, ridgeSupport322_014_checked, ridgeSupport322_015_checked, ridgeSupport322_016_checked, ridgeSupport322_017_checked, ridgeSupport322_018_checked, ridgeSupport322_019_checked, ridgeSupport322_020_checked, ridgeSupport322_021_checked, ridgeSupport322_022_checked, ridgeSupport322_023_checked, ridgeSupport322_024_checked, ridgeSupport322_025_checked, ridgeSupport322_026_checked, ridgeSupport322_027_checked, ridgeSupport322_028_checked, ridgeSupport322_029_checked, ridgeSupport322_030_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
