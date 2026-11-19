module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport584Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 584 031 14
cert_ridgeSupport_suffix_decode_2 584 030 14 26 26 031 031 0
cert_ridgeSupport_suffix_decode_2 584 029 14 58 32 031 030 26
cert_ridgeSupport_suffix_decode_2 584 028 14 90 32 031 029 58
cert_ridgeSupport_suffix_decode_2 584 027 14 122 32 031 028 90
cert_ridgeSupport_suffix_decode_2 584 026 14 154 32 031 027 122
cert_ridgeSupport_suffix_decode_2 584 025 14 186 32 031 026 154
cert_ridgeSupport_suffix_decode_2 584 024 14 218 32 031 025 186
cert_ridgeSupport_suffix_decode_2 584 023 14 250 32 031 024 218
cert_ridgeSupport_suffix_decode_2 584 022 14 282 32 031 023 250
cert_ridgeSupport_suffix_decode_2 584 021 14 314 32 031 022 282
cert_ridgeSupport_suffix_decode_2 584 020 14 346 32 031 021 314
cert_ridgeSupport_suffix_decode_2 584 019 14 378 32 031 020 346
cert_ridgeSupport_suffix_decode_2 584 018 14 410 32 031 019 378
cert_ridgeSupport_suffix_decode_2 584 017 14 442 32 031 018 410
cert_ridgeSupport_suffix_decode_2 584 016 14 474 32 031 017 442
cert_ridgeSupport_suffix_decode_2 584 015 14 506 32 031 016 474
cert_ridgeSupport_suffix_decode_2 584 014 14 538 32 031 015 506
cert_ridgeSupport_suffix_decode_2 584 013 14 570 32 031 014 538
cert_ridgeSupport_suffix_decode_2 584 012 14 602 32 031 013 570
cert_ridgeSupport_suffix_decode_2 584 011 14 634 32 031 012 602
cert_ridgeSupport_suffix_decode_2 584 010 14 666 32 031 011 634
cert_ridgeSupport_suffix_decode_2 584 009 14 698 32 031 010 666
cert_ridgeSupport_suffix_decode_2 584 008 14 730 32 031 009 698
cert_ridgeSupport_suffix_decode_2 584 007 14 762 32 031 008 730
cert_ridgeSupport_suffix_decode_2 584 006 14 794 32 031 007 762
cert_ridgeSupport_suffix_decode_2 584 005 14 826 32 031 006 794
cert_ridgeSupport_suffix_decode_2 584 004 14 858 32 031 005 826
cert_ridgeSupport_suffix_decode_2 584 003 14 890 32 031 004 858
cert_ridgeSupport_suffix_decode_2 584 002 14 922 32 031 003 890
cert_ridgeSupport_suffix_decode_2 584 001 14 954 32 031 002 922
cert_ridgeSupport_suffix_decode_2 584 000 14 986 32 031 001 954
cert_ridgeSupport_eq_3 584
theorem ridgeTest_large_584 : ridgeTest 584 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport584_eq]
    simp only [ridgeSupport584_suffix_000, ridgeSupport584_suffix_001, ridgeSupport584_suffix_002, ridgeSupport584_suffix_003, ridgeSupport584_suffix_004, ridgeSupport584_suffix_005, ridgeSupport584_suffix_006, ridgeSupport584_suffix_007, ridgeSupport584_suffix_008, ridgeSupport584_suffix_009, ridgeSupport584_suffix_010, ridgeSupport584_suffix_011, ridgeSupport584_suffix_012, ridgeSupport584_suffix_013, ridgeSupport584_suffix_014, ridgeSupport584_suffix_015, ridgeSupport584_suffix_016, ridgeSupport584_suffix_017, ridgeSupport584_suffix_018, ridgeSupport584_suffix_019, ridgeSupport584_suffix_020, ridgeSupport584_suffix_021, ridgeSupport584_suffix_022, ridgeSupport584_suffix_023, ridgeSupport584_suffix_024, ridgeSupport584_suffix_025, ridgeSupport584_suffix_026, ridgeSupport584_suffix_027, ridgeSupport584_suffix_028, ridgeSupport584_suffix_029, ridgeSupport584_suffix_030, ridgeSupport584_suffix_031, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport584_000_mask, ridgeSupport584_001_mask, ridgeSupport584_002_mask, ridgeSupport584_003_mask, ridgeSupport584_004_mask, ridgeSupport584_005_mask, ridgeSupport584_006_mask, ridgeSupport584_007_mask, ridgeSupport584_008_mask, ridgeSupport584_009_mask, ridgeSupport584_010_mask, ridgeSupport584_011_mask, ridgeSupport584_012_mask, ridgeSupport584_013_mask, ridgeSupport584_014_mask, ridgeSupport584_015_mask, ridgeSupport584_016_mask, ridgeSupport584_017_mask, ridgeSupport584_018_mask, ridgeSupport584_019_mask, ridgeSupport584_020_mask, ridgeSupport584_021_mask, ridgeSupport584_022_mask, ridgeSupport584_023_mask, ridgeSupport584_024_mask, ridgeSupport584_025_mask, ridgeSupport584_026_mask, ridgeSupport584_027_mask, ridgeSupport584_028_mask, ridgeSupport584_029_mask, ridgeSupport584_030_mask]
    decide +kernel
  · rw [ridgeSupport584_eq]
    simp only [ridgeSupport584_suffix_000, ridgeSupport584_suffix_001, ridgeSupport584_suffix_002, ridgeSupport584_suffix_003, ridgeSupport584_suffix_004, ridgeSupport584_suffix_005, ridgeSupport584_suffix_006, ridgeSupport584_suffix_007, ridgeSupport584_suffix_008, ridgeSupport584_suffix_009, ridgeSupport584_suffix_010, ridgeSupport584_suffix_011, ridgeSupport584_suffix_012, ridgeSupport584_suffix_013, ridgeSupport584_suffix_014, ridgeSupport584_suffix_015, ridgeSupport584_suffix_016, ridgeSupport584_suffix_017, ridgeSupport584_suffix_018, ridgeSupport584_suffix_019, ridgeSupport584_suffix_020, ridgeSupport584_suffix_021, ridgeSupport584_suffix_022, ridgeSupport584_suffix_023, ridgeSupport584_suffix_024, ridgeSupport584_suffix_025, ridgeSupport584_suffix_026, ridgeSupport584_suffix_027, ridgeSupport584_suffix_028, ridgeSupport584_suffix_029, ridgeSupport584_suffix_030, ridgeSupport584_suffix_031, List.all_append, List.all_nil, ridgeSupport584_000_checked, ridgeSupport584_001_checked, ridgeSupport584_002_checked, ridgeSupport584_003_checked, ridgeSupport584_004_checked, ridgeSupport584_005_checked, ridgeSupport584_006_checked, ridgeSupport584_007_checked, ridgeSupport584_008_checked, ridgeSupport584_009_checked, ridgeSupport584_010_checked, ridgeSupport584_011_checked, ridgeSupport584_012_checked, ridgeSupport584_013_checked, ridgeSupport584_014_checked, ridgeSupport584_015_checked, ridgeSupport584_016_checked, ridgeSupport584_017_checked, ridgeSupport584_018_checked, ridgeSupport584_019_checked, ridgeSupport584_020_checked, ridgeSupport584_021_checked, ridgeSupport584_022_checked, ridgeSupport584_023_checked, ridgeSupport584_024_checked, ridgeSupport584_025_checked, ridgeSupport584_026_checked, ridgeSupport584_027_checked, ridgeSupport584_028_checked, ridgeSupport584_029_checked, ridgeSupport584_030_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
