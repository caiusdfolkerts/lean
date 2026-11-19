module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport386Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 386 031 14
cert_ridgeSupport_suffix_decode_2 386 030 14 26 26 031 031 0
cert_ridgeSupport_suffix_decode_2 386 029 14 58 32 031 030 26
cert_ridgeSupport_suffix_decode_2 386 028 14 90 32 031 029 58
cert_ridgeSupport_suffix_decode_2 386 027 14 122 32 031 028 90
cert_ridgeSupport_suffix_decode_2 386 026 14 154 32 031 027 122
cert_ridgeSupport_suffix_decode_2 386 025 14 186 32 031 026 154
cert_ridgeSupport_suffix_decode_2 386 024 14 218 32 031 025 186
cert_ridgeSupport_suffix_decode_2 386 023 14 250 32 031 024 218
cert_ridgeSupport_suffix_decode_2 386 022 14 282 32 031 023 250
cert_ridgeSupport_suffix_decode_2 386 021 14 314 32 031 022 282
cert_ridgeSupport_suffix_decode_2 386 020 14 346 32 031 021 314
cert_ridgeSupport_suffix_decode_2 386 019 14 378 32 031 020 346
cert_ridgeSupport_suffix_decode_2 386 018 14 410 32 031 019 378
cert_ridgeSupport_suffix_decode_2 386 017 14 442 32 031 018 410
cert_ridgeSupport_suffix_decode_2 386 016 14 474 32 031 017 442
cert_ridgeSupport_suffix_decode_2 386 015 14 506 32 031 016 474
cert_ridgeSupport_suffix_decode_2 386 014 14 538 32 031 015 506
cert_ridgeSupport_suffix_decode_2 386 013 14 570 32 031 014 538
cert_ridgeSupport_suffix_decode_2 386 012 14 602 32 031 013 570
cert_ridgeSupport_suffix_decode_2 386 011 14 634 32 031 012 602
cert_ridgeSupport_suffix_decode_2 386 010 14 666 32 031 011 634
cert_ridgeSupport_suffix_decode_2 386 009 14 698 32 031 010 666
cert_ridgeSupport_suffix_decode_2 386 008 14 730 32 031 009 698
cert_ridgeSupport_suffix_decode_2 386 007 14 762 32 031 008 730
cert_ridgeSupport_suffix_decode_2 386 006 14 794 32 031 007 762
cert_ridgeSupport_suffix_decode_2 386 005 14 826 32 031 006 794
cert_ridgeSupport_suffix_decode_2 386 004 14 858 32 031 005 826
cert_ridgeSupport_suffix_decode_2 386 003 14 890 32 031 004 858
cert_ridgeSupport_suffix_decode_2 386 002 14 922 32 031 003 890
cert_ridgeSupport_suffix_decode_2 386 001 14 954 32 031 002 922
cert_ridgeSupport_suffix_decode_2 386 000 14 986 32 031 001 954
cert_ridgeSupport_eq_3 386
theorem ridgeTest_large_386 : ridgeTest 386 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport386_eq]
    simp only [ridgeSupport386_suffix_000, ridgeSupport386_suffix_001, ridgeSupport386_suffix_002, ridgeSupport386_suffix_003, ridgeSupport386_suffix_004, ridgeSupport386_suffix_005, ridgeSupport386_suffix_006, ridgeSupport386_suffix_007, ridgeSupport386_suffix_008, ridgeSupport386_suffix_009, ridgeSupport386_suffix_010, ridgeSupport386_suffix_011, ridgeSupport386_suffix_012, ridgeSupport386_suffix_013, ridgeSupport386_suffix_014, ridgeSupport386_suffix_015, ridgeSupport386_suffix_016, ridgeSupport386_suffix_017, ridgeSupport386_suffix_018, ridgeSupport386_suffix_019, ridgeSupport386_suffix_020, ridgeSupport386_suffix_021, ridgeSupport386_suffix_022, ridgeSupport386_suffix_023, ridgeSupport386_suffix_024, ridgeSupport386_suffix_025, ridgeSupport386_suffix_026, ridgeSupport386_suffix_027, ridgeSupport386_suffix_028, ridgeSupport386_suffix_029, ridgeSupport386_suffix_030, ridgeSupport386_suffix_031, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport386_000_mask, ridgeSupport386_001_mask, ridgeSupport386_002_mask, ridgeSupport386_003_mask, ridgeSupport386_004_mask, ridgeSupport386_005_mask, ridgeSupport386_006_mask, ridgeSupport386_007_mask, ridgeSupport386_008_mask, ridgeSupport386_009_mask, ridgeSupport386_010_mask, ridgeSupport386_011_mask, ridgeSupport386_012_mask, ridgeSupport386_013_mask, ridgeSupport386_014_mask, ridgeSupport386_015_mask, ridgeSupport386_016_mask, ridgeSupport386_017_mask, ridgeSupport386_018_mask, ridgeSupport386_019_mask, ridgeSupport386_020_mask, ridgeSupport386_021_mask, ridgeSupport386_022_mask, ridgeSupport386_023_mask, ridgeSupport386_024_mask, ridgeSupport386_025_mask, ridgeSupport386_026_mask, ridgeSupport386_027_mask, ridgeSupport386_028_mask, ridgeSupport386_029_mask, ridgeSupport386_030_mask]
    decide +kernel
  · rw [ridgeSupport386_eq]
    simp only [ridgeSupport386_suffix_000, ridgeSupport386_suffix_001, ridgeSupport386_suffix_002, ridgeSupport386_suffix_003, ridgeSupport386_suffix_004, ridgeSupport386_suffix_005, ridgeSupport386_suffix_006, ridgeSupport386_suffix_007, ridgeSupport386_suffix_008, ridgeSupport386_suffix_009, ridgeSupport386_suffix_010, ridgeSupport386_suffix_011, ridgeSupport386_suffix_012, ridgeSupport386_suffix_013, ridgeSupport386_suffix_014, ridgeSupport386_suffix_015, ridgeSupport386_suffix_016, ridgeSupport386_suffix_017, ridgeSupport386_suffix_018, ridgeSupport386_suffix_019, ridgeSupport386_suffix_020, ridgeSupport386_suffix_021, ridgeSupport386_suffix_022, ridgeSupport386_suffix_023, ridgeSupport386_suffix_024, ridgeSupport386_suffix_025, ridgeSupport386_suffix_026, ridgeSupport386_suffix_027, ridgeSupport386_suffix_028, ridgeSupport386_suffix_029, ridgeSupport386_suffix_030, ridgeSupport386_suffix_031, List.all_append, List.all_nil, ridgeSupport386_000_checked, ridgeSupport386_001_checked, ridgeSupport386_002_checked, ridgeSupport386_003_checked, ridgeSupport386_004_checked, ridgeSupport386_005_checked, ridgeSupport386_006_checked, ridgeSupport386_007_checked, ridgeSupport386_008_checked, ridgeSupport386_009_checked, ridgeSupport386_010_checked, ridgeSupport386_011_checked, ridgeSupport386_012_checked, ridgeSupport386_013_checked, ridgeSupport386_014_checked, ridgeSupport386_015_checked, ridgeSupport386_016_checked, ridgeSupport386_017_checked, ridgeSupport386_018_checked, ridgeSupport386_019_checked, ridgeSupport386_020_checked, ridgeSupport386_021_checked, ridgeSupport386_022_checked, ridgeSupport386_023_checked, ridgeSupport386_024_checked, ridgeSupport386_025_checked, ridgeSupport386_026_checked, ridgeSupport386_027_checked, ridgeSupport386_028_checked, ridgeSupport386_029_checked, ridgeSupport386_030_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
