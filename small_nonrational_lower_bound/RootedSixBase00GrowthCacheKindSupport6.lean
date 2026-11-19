module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheKindSupport6Batch000
public import BundledChecks.RootedSixBase00GrowthCacheKindSupport6Batch001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_suffix_decode_5 6 162 15
cert_kindSupport_suffix_decode_4 6 161 15 32 32 162 162 0
cert_kindSupport_suffix_decode_4 6 160 15 64 32 162 161 32
cert_kindSupport_suffix_decode_4 6 159 15 96 32 162 160 64
cert_kindSupport_suffix_decode_4 6 158 15 128 32 162 159 96
cert_kindSupport_suffix_decode_4 6 157 15 160 32 162 158 128
cert_kindSupport_suffix_decode_4 6 156 15 192 32 162 157 160
cert_kindSupport_suffix_decode_4 6 155 15 224 32 162 156 192
cert_kindSupport_suffix_decode_4 6 154 15 256 32 162 155 224
cert_kindSupport_suffix_decode_4 6 153 15 288 32 162 154 256
cert_kindSupport_suffix_decode_4 6 152 15 320 32 162 153 288
cert_kindSupport_suffix_decode_4 6 151 15 352 32 162 152 320
cert_kindSupport_suffix_decode_4 6 150 15 384 32 162 151 352
cert_kindSupport_suffix_decode_4 6 149 15 416 32 162 150 384
cert_kindSupport_suffix_decode_4 6 148 15 448 32 162 149 416
cert_kindSupport_suffix_decode_4 6 147 15 480 32 162 148 448
cert_kindSupport_suffix_decode_4 6 146 15 512 32 162 147 480
cert_kindSupport_suffix_decode_4 6 145 15 544 32 162 146 512
cert_kindSupport_suffix_decode_4 6 144 15 576 32 162 145 544
cert_kindSupport_suffix_decode_4 6 143 15 608 32 162 144 576
cert_kindSupport_suffix_decode_4 6 142 15 640 32 162 143 608
cert_kindSupport_suffix_decode_4 6 141 15 672 32 162 142 640
cert_kindSupport_suffix_decode_4 6 140 15 704 32 162 141 672
cert_kindSupport_suffix_decode_4 6 139 15 736 32 162 140 704
cert_kindSupport_suffix_decode_4 6 138 15 768 32 162 139 736
cert_kindSupport_suffix_decode_4 6 137 15 800 32 162 138 768
cert_kindSupport_suffix_decode_4 6 136 15 832 32 162 137 800
cert_kindSupport_suffix_decode_4 6 135 15 864 32 162 136 832
cert_kindSupport_suffix_decode_4 6 134 15 896 32 162 135 864
cert_kindSupport_suffix_decode_4 6 133 15 928 32 162 134 896
cert_kindSupport_suffix_decode_4 6 132 15 960 32 162 133 928
cert_kindSupport_suffix_decode_4 6 131 15 992 32 162 132 960
cert_kindSupport_suffix_decode_4 6 130 15 1024 32 162 131 992
cert_kindSupport_suffix_decode_4 6 129 15 1056 32 162 130 1024
cert_kindSupport_suffix_decode_4 6 128 15 1088 32 162 129 1056
cert_kindSupport_suffix_decode_4 6 127 15 1120 32 162 128 1088
cert_kindSupport_suffix_decode_4 6 126 15 1152 32 162 127 1120
cert_kindSupport_suffix_decode_4 6 125 15 1184 32 162 126 1152
cert_kindSupport_suffix_decode_4 6 124 15 1216 32 162 125 1184
cert_kindSupport_suffix_decode_4 6 123 15 1248 32 162 124 1216
cert_kindSupport_suffix_decode_4 6 122 15 1280 32 162 123 1248
cert_kindSupport_suffix_decode_4 6 121 15 1312 32 162 122 1280
cert_kindSupport_suffix_decode_4 6 120 15 1344 32 162 121 1312
cert_kindSupport_suffix_decode_4 6 119 15 1376 32 162 120 1344
cert_kindSupport_suffix_decode_4 6 118 15 1408 32 162 119 1376
cert_kindSupport_suffix_decode_4 6 117 15 1440 32 162 118 1408
cert_kindSupport_suffix_decode_4 6 116 15 1472 32 162 117 1440
cert_kindSupport_suffix_decode_4 6 115 15 1504 32 162 116 1472
cert_kindSupport_suffix_decode_4 6 114 15 1536 32 162 115 1504
cert_kindSupport_suffix_decode_4 6 113 15 1568 32 162 114 1536
cert_kindSupport_suffix_decode_4 6 112 15 1600 32 162 113 1568
cert_kindSupport_suffix_decode_4 6 111 15 1632 32 162 112 1600
cert_kindSupport_suffix_decode_4 6 110 15 1664 32 162 111 1632
cert_kindSupport_suffix_decode_4 6 109 15 1696 32 162 110 1664
cert_kindSupport_suffix_decode_4 6 108 15 1728 32 162 109 1696
cert_kindSupport_suffix_decode_4 6 107 15 1760 32 162 108 1728
cert_kindSupport_suffix_decode_4 6 106 15 1792 32 162 107 1760
cert_kindSupport_suffix_decode_4 6 105 15 1824 32 162 106 1792
cert_kindSupport_suffix_decode_4 6 104 15 1856 32 162 105 1824
cert_kindSupport_suffix_decode_4 6 103 15 1888 32 162 104 1856
cert_kindSupport_suffix_decode_4 6 102 15 1920 32 162 103 1888
cert_kindSupport_suffix_decode_4 6 101 15 1952 32 162 102 1920
cert_kindSupport_suffix_decode_4 6 100 15 1984 32 162 101 1952
cert_kindSupport_suffix_decode_4 6 099 15 2016 32 162 100 1984
cert_kindSupport_suffix_decode_4 6 098 15 2048 32 162 099 2016
cert_kindSupport_suffix_decode_4 6 097 15 2080 32 162 098 2048
cert_kindSupport_suffix_decode_4 6 096 15 2112 32 162 097 2080
cert_kindSupport_suffix_decode_4 6 095 15 2144 32 162 096 2112
cert_kindSupport_suffix_decode_4 6 094 15 2176 32 162 095 2144
cert_kindSupport_suffix_decode_4 6 093 15 2208 32 162 094 2176
cert_kindSupport_suffix_decode_4 6 092 15 2240 32 162 093 2208
cert_kindSupport_suffix_decode_4 6 091 15 2272 32 162 092 2240
cert_kindSupport_suffix_decode_4 6 090 15 2304 32 162 091 2272
cert_kindSupport_suffix_decode_4 6 089 15 2336 32 162 090 2304
cert_kindSupport_suffix_decode_4 6 088 15 2368 32 162 089 2336
cert_kindSupport_suffix_decode_4 6 087 15 2400 32 162 088 2368
cert_kindSupport_suffix_decode_4 6 086 15 2432 32 162 087 2400
cert_kindSupport_suffix_decode_4 6 085 15 2464 32 162 086 2432
cert_kindSupport_suffix_decode_4 6 084 15 2496 32 162 085 2464
cert_kindSupport_suffix_decode_4 6 083 15 2528 32 162 084 2496
cert_kindSupport_suffix_decode_4 6 082 15 2560 32 162 083 2528
cert_kindSupport_suffix_decode_4 6 081 15 2592 32 162 082 2560
cert_kindSupport_suffix_decode_4 6 080 15 2624 32 162 081 2592
cert_kindSupport_suffix_decode_4 6 079 15 2656 32 162 080 2624
cert_kindSupport_suffix_decode_4 6 078 15 2688 32 162 079 2656
cert_kindSupport_suffix_decode_4 6 077 15 2720 32 162 078 2688
cert_kindSupport_suffix_decode_4 6 076 15 2752 32 162 077 2720
cert_kindSupport_suffix_decode_4 6 075 15 2784 32 162 076 2752
cert_kindSupport_suffix_decode_4 6 074 15 2816 32 162 075 2784
cert_kindSupport_suffix_decode_4 6 073 15 2848 32 162 074 2816
cert_kindSupport_suffix_decode_4 6 072 15 2880 32 162 073 2848
cert_kindSupport_suffix_decode_4 6 071 15 2912 32 162 072 2880
cert_kindSupport_suffix_decode_4 6 070 15 2944 32 162 071 2912
cert_kindSupport_suffix_decode_4 6 069 15 2976 32 162 070 2944
cert_kindSupport_suffix_decode_4 6 068 15 3008 32 162 069 2976
cert_kindSupport_suffix_decode_4 6 067 15 3040 32 162 068 3008
cert_kindSupport_suffix_decode_4 6 066 15 3072 32 162 067 3040
cert_kindSupport_suffix_decode_4 6 065 15 3104 32 162 066 3072
cert_kindSupport_suffix_decode_4 6 064 15 3136 32 162 065 3104
cert_kindSupport_suffix_decode_4 6 063 15 3168 32 162 064 3136
cert_kindSupport_suffix_decode_4 6 062 15 3200 32 162 063 3168
cert_kindSupport_suffix_decode_4 6 061 15 3232 32 162 062 3200
cert_kindSupport_suffix_decode_4 6 060 15 3264 32 162 061 3232
cert_kindSupport_suffix_decode_4 6 059 15 3296 32 162 060 3264
cert_kindSupport_suffix_decode_4 6 058 15 3328 32 162 059 3296
cert_kindSupport_suffix_decode_4 6 057 15 3360 32 162 058 3328
cert_kindSupport_suffix_decode_4 6 056 15 3392 32 162 057 3360
cert_kindSupport_suffix_decode_4 6 055 15 3424 32 162 056 3392
cert_kindSupport_suffix_decode_4 6 054 15 3456 32 162 055 3424
cert_kindSupport_suffix_decode_4 6 053 15 3488 32 162 054 3456
cert_kindSupport_suffix_decode_4 6 052 15 3520 32 162 053 3488
cert_kindSupport_suffix_decode_4 6 051 15 3552 32 162 052 3520
cert_kindSupport_suffix_decode_4 6 050 15 3584 32 162 051 3552
cert_kindSupport_suffix_decode_4 6 049 15 3616 32 162 050 3584
cert_kindSupport_suffix_decode_4 6 048 15 3648 32 162 049 3616
cert_kindSupport_suffix_decode_4 6 047 15 3680 32 162 048 3648
cert_kindSupport_suffix_decode_4 6 046 15 3712 32 162 047 3680
cert_kindSupport_suffix_decode_4 6 045 15 3744 32 162 046 3712
cert_kindSupport_suffix_decode_4 6 044 15 3776 32 162 045 3744
cert_kindSupport_suffix_decode_4 6 043 15 3808 32 162 044 3776
cert_kindSupport_suffix_decode_4 6 042 15 3840 32 162 043 3808
cert_kindSupport_suffix_decode_4 6 041 15 3872 32 162 042 3840
cert_kindSupport_suffix_decode_4 6 040 15 3904 32 162 041 3872
cert_kindSupport_suffix_decode_4 6 039 15 3936 32 162 040 3904
cert_kindSupport_suffix_decode_4 6 038 15 3968 32 162 039 3936
cert_kindSupport_suffix_decode_4 6 037 15 4000 32 162 038 3968
cert_kindSupport_suffix_decode_4 6 036 15 4032 32 162 037 4000
cert_kindSupport_suffix_decode_4 6 035 15 4064 32 162 036 4032
cert_kindSupport_suffix_decode_4 6 034 15 4096 32 162 035 4064
cert_kindSupport_suffix_decode_4 6 033 15 4128 32 162 034 4096
cert_kindSupport_suffix_decode_4 6 032 15 4160 32 162 033 4128
cert_kindSupport_suffix_decode_4 6 031 15 4192 32 162 032 4160
cert_kindSupport_suffix_decode_4 6 030 15 4224 32 162 031 4192
cert_kindSupport_suffix_decode_4 6 029 15 4256 32 162 030 4224
cert_kindSupport_suffix_decode_4 6 028 15 4288 32 162 029 4256
cert_kindSupport_suffix_decode_4 6 027 15 4320 32 162 028 4288
cert_kindSupport_suffix_decode_4 6 026 15 4352 32 162 027 4320
cert_kindSupport_suffix_decode_4 6 025 15 4384 32 162 026 4352
cert_kindSupport_suffix_decode_4 6 024 15 4416 32 162 025 4384
cert_kindSupport_suffix_decode_4 6 023 15 4448 32 162 024 4416
cert_kindSupport_suffix_decode_4 6 022 15 4480 32 162 023 4448
cert_kindSupport_suffix_decode_4 6 021 15 4512 32 162 022 4480
cert_kindSupport_suffix_decode_4 6 020 15 4544 32 162 021 4512
cert_kindSupport_suffix_decode_4 6 019 15 4576 32 162 020 4544
cert_kindSupport_suffix_decode_4 6 018 15 4608 32 162 019 4576
cert_kindSupport_suffix_decode_4 6 017 15 4640 32 162 018 4608
cert_kindSupport_suffix_decode_4 6 016 15 4672 32 162 017 4640
cert_kindSupport_suffix_decode_4 6 015 15 4704 32 162 016 4672
cert_kindSupport_suffix_decode_4 6 014 15 4736 32 162 015 4704
cert_kindSupport_suffix_decode_4 6 013 15 4768 32 162 014 4736
cert_kindSupport_suffix_decode_4 6 012 15 4800 32 162 013 4768
cert_kindSupport_suffix_decode_4 6 011 15 4832 32 162 012 4800
cert_kindSupport_suffix_decode_4 6 010 15 4864 32 162 011 4832
cert_kindSupport_suffix_decode_4 6 009 15 4896 32 162 010 4864
cert_kindSupport_suffix_decode_4 6 008 15 4928 32 162 009 4896
cert_kindSupport_suffix_decode_4 6 007 15 4960 32 162 008 4928
cert_kindSupport_suffix_decode_4 6 006 15 4992 32 162 007 4960
cert_kindSupport_suffix_decode_4 6 005 15 5024 32 162 006 4992
cert_kindSupport_suffix_decode_4 6 004 15 5056 32 162 005 5024
cert_kindSupport_suffix_decode_4 6 003 15 5088 32 162 004 5056
cert_kindSupport_suffix_decode_4 6 002 15 5120 32 162 003 5088
cert_kindSupport_suffix_decode_4 6 001 15 5152 32 162 002 5120
cert_kindSupport_suffix_decode_4 6 000 15 5184 32 162 001 5152
cert_kindSupport_eq_2 6
theorem kindTest_large_6 : kindTest 6 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport6_eq]
    simp only [kindSupport6_suffix_000, kindSupport6_suffix_001, kindSupport6_suffix_002, kindSupport6_suffix_003, kindSupport6_suffix_004, kindSupport6_suffix_005, kindSupport6_suffix_006, kindSupport6_suffix_007, kindSupport6_suffix_008, kindSupport6_suffix_009, kindSupport6_suffix_010, kindSupport6_suffix_011, kindSupport6_suffix_012, kindSupport6_suffix_013, kindSupport6_suffix_014, kindSupport6_suffix_015, kindSupport6_suffix_016, kindSupport6_suffix_017, kindSupport6_suffix_018, kindSupport6_suffix_019, kindSupport6_suffix_020, kindSupport6_suffix_021, kindSupport6_suffix_022, kindSupport6_suffix_023, kindSupport6_suffix_024, kindSupport6_suffix_025, kindSupport6_suffix_026, kindSupport6_suffix_027, kindSupport6_suffix_028, kindSupport6_suffix_029, kindSupport6_suffix_030, kindSupport6_suffix_031, kindSupport6_suffix_032, kindSupport6_suffix_033, kindSupport6_suffix_034, kindSupport6_suffix_035, kindSupport6_suffix_036, kindSupport6_suffix_037, kindSupport6_suffix_038, kindSupport6_suffix_039, kindSupport6_suffix_040, kindSupport6_suffix_041, kindSupport6_suffix_042, kindSupport6_suffix_043, kindSupport6_suffix_044, kindSupport6_suffix_045, kindSupport6_suffix_046, kindSupport6_suffix_047, kindSupport6_suffix_048, kindSupport6_suffix_049, kindSupport6_suffix_050, kindSupport6_suffix_051, kindSupport6_suffix_052, kindSupport6_suffix_053, kindSupport6_suffix_054, kindSupport6_suffix_055, kindSupport6_suffix_056, kindSupport6_suffix_057, kindSupport6_suffix_058, kindSupport6_suffix_059, kindSupport6_suffix_060, kindSupport6_suffix_061, kindSupport6_suffix_062, kindSupport6_suffix_063, kindSupport6_suffix_064, kindSupport6_suffix_065, kindSupport6_suffix_066, kindSupport6_suffix_067, kindSupport6_suffix_068, kindSupport6_suffix_069, kindSupport6_suffix_070, kindSupport6_suffix_071, kindSupport6_suffix_072, kindSupport6_suffix_073, kindSupport6_suffix_074, kindSupport6_suffix_075, kindSupport6_suffix_076, kindSupport6_suffix_077, kindSupport6_suffix_078, kindSupport6_suffix_079, kindSupport6_suffix_080, kindSupport6_suffix_081, kindSupport6_suffix_082, kindSupport6_suffix_083, kindSupport6_suffix_084, kindSupport6_suffix_085, kindSupport6_suffix_086, kindSupport6_suffix_087, kindSupport6_suffix_088, kindSupport6_suffix_089, kindSupport6_suffix_090, kindSupport6_suffix_091, kindSupport6_suffix_092, kindSupport6_suffix_093, kindSupport6_suffix_094, kindSupport6_suffix_095, kindSupport6_suffix_096, kindSupport6_suffix_097, kindSupport6_suffix_098, kindSupport6_suffix_099, kindSupport6_suffix_100, kindSupport6_suffix_101, kindSupport6_suffix_102, kindSupport6_suffix_103, kindSupport6_suffix_104, kindSupport6_suffix_105, kindSupport6_suffix_106, kindSupport6_suffix_107, kindSupport6_suffix_108, kindSupport6_suffix_109, kindSupport6_suffix_110, kindSupport6_suffix_111, kindSupport6_suffix_112, kindSupport6_suffix_113, kindSupport6_suffix_114, kindSupport6_suffix_115, kindSupport6_suffix_116, kindSupport6_suffix_117, kindSupport6_suffix_118, kindSupport6_suffix_119, kindSupport6_suffix_120, kindSupport6_suffix_121, kindSupport6_suffix_122, kindSupport6_suffix_123, kindSupport6_suffix_124, kindSupport6_suffix_125, kindSupport6_suffix_126, kindSupport6_suffix_127, kindSupport6_suffix_128, kindSupport6_suffix_129, kindSupport6_suffix_130, kindSupport6_suffix_131, kindSupport6_suffix_132, kindSupport6_suffix_133, kindSupport6_suffix_134, kindSupport6_suffix_135, kindSupport6_suffix_136, kindSupport6_suffix_137, kindSupport6_suffix_138, kindSupport6_suffix_139, kindSupport6_suffix_140, kindSupport6_suffix_141, kindSupport6_suffix_142, kindSupport6_suffix_143, kindSupport6_suffix_144, kindSupport6_suffix_145, kindSupport6_suffix_146, kindSupport6_suffix_147, kindSupport6_suffix_148, kindSupport6_suffix_149, kindSupport6_suffix_150, kindSupport6_suffix_151, kindSupport6_suffix_152, kindSupport6_suffix_153, kindSupport6_suffix_154, kindSupport6_suffix_155, kindSupport6_suffix_156, kindSupport6_suffix_157, kindSupport6_suffix_158, kindSupport6_suffix_159, kindSupport6_suffix_160, kindSupport6_suffix_161, kindSupport6_suffix_162, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport6_000_mask, kindSupport6_001_mask, kindSupport6_002_mask, kindSupport6_003_mask, kindSupport6_004_mask, kindSupport6_005_mask, kindSupport6_006_mask, kindSupport6_007_mask, kindSupport6_008_mask, kindSupport6_009_mask, kindSupport6_010_mask, kindSupport6_011_mask, kindSupport6_012_mask, kindSupport6_013_mask, kindSupport6_014_mask, kindSupport6_015_mask, kindSupport6_016_mask, kindSupport6_017_mask, kindSupport6_018_mask, kindSupport6_019_mask, kindSupport6_020_mask, kindSupport6_021_mask, kindSupport6_022_mask, kindSupport6_023_mask, kindSupport6_024_mask, kindSupport6_025_mask, kindSupport6_026_mask, kindSupport6_027_mask, kindSupport6_028_mask, kindSupport6_029_mask, kindSupport6_030_mask, kindSupport6_031_mask, kindSupport6_032_mask, kindSupport6_033_mask, kindSupport6_034_mask, kindSupport6_035_mask, kindSupport6_036_mask, kindSupport6_037_mask, kindSupport6_038_mask, kindSupport6_039_mask, kindSupport6_040_mask, kindSupport6_041_mask, kindSupport6_042_mask, kindSupport6_043_mask, kindSupport6_044_mask, kindSupport6_045_mask, kindSupport6_046_mask, kindSupport6_047_mask, kindSupport6_048_mask, kindSupport6_049_mask, kindSupport6_050_mask, kindSupport6_051_mask, kindSupport6_052_mask, kindSupport6_053_mask, kindSupport6_054_mask, kindSupport6_055_mask, kindSupport6_056_mask, kindSupport6_057_mask, kindSupport6_058_mask, kindSupport6_059_mask, kindSupport6_060_mask, kindSupport6_061_mask, kindSupport6_062_mask, kindSupport6_063_mask, kindSupport6_064_mask, kindSupport6_065_mask, kindSupport6_066_mask, kindSupport6_067_mask, kindSupport6_068_mask, kindSupport6_069_mask, kindSupport6_070_mask, kindSupport6_071_mask, kindSupport6_072_mask, kindSupport6_073_mask, kindSupport6_074_mask, kindSupport6_075_mask, kindSupport6_076_mask, kindSupport6_077_mask, kindSupport6_078_mask, kindSupport6_079_mask, kindSupport6_080_mask, kindSupport6_081_mask, kindSupport6_082_mask, kindSupport6_083_mask, kindSupport6_084_mask, kindSupport6_085_mask, kindSupport6_086_mask, kindSupport6_087_mask, kindSupport6_088_mask, kindSupport6_089_mask, kindSupport6_090_mask, kindSupport6_091_mask, kindSupport6_092_mask, kindSupport6_093_mask, kindSupport6_094_mask, kindSupport6_095_mask, kindSupport6_096_mask, kindSupport6_097_mask, kindSupport6_098_mask, kindSupport6_099_mask, kindSupport6_100_mask, kindSupport6_101_mask, kindSupport6_102_mask, kindSupport6_103_mask, kindSupport6_104_mask, kindSupport6_105_mask, kindSupport6_106_mask, kindSupport6_107_mask, kindSupport6_108_mask, kindSupport6_109_mask, kindSupport6_110_mask, kindSupport6_111_mask, kindSupport6_112_mask, kindSupport6_113_mask, kindSupport6_114_mask, kindSupport6_115_mask, kindSupport6_116_mask, kindSupport6_117_mask, kindSupport6_118_mask, kindSupport6_119_mask, kindSupport6_120_mask, kindSupport6_121_mask, kindSupport6_122_mask, kindSupport6_123_mask, kindSupport6_124_mask, kindSupport6_125_mask, kindSupport6_126_mask, kindSupport6_127_mask, kindSupport6_128_mask, kindSupport6_129_mask, kindSupport6_130_mask, kindSupport6_131_mask, kindSupport6_132_mask, kindSupport6_133_mask, kindSupport6_134_mask, kindSupport6_135_mask, kindSupport6_136_mask, kindSupport6_137_mask, kindSupport6_138_mask, kindSupport6_139_mask, kindSupport6_140_mask, kindSupport6_141_mask, kindSupport6_142_mask, kindSupport6_143_mask, kindSupport6_144_mask, kindSupport6_145_mask, kindSupport6_146_mask, kindSupport6_147_mask, kindSupport6_148_mask, kindSupport6_149_mask, kindSupport6_150_mask, kindSupport6_151_mask, kindSupport6_152_mask, kindSupport6_153_mask, kindSupport6_154_mask, kindSupport6_155_mask, kindSupport6_156_mask, kindSupport6_157_mask, kindSupport6_158_mask, kindSupport6_159_mask, kindSupport6_160_mask, kindSupport6_161_mask]
    decide +kernel
  · rw [kindSupport6_eq]
    simp only [kindSupport6_suffix_000, kindSupport6_suffix_001, kindSupport6_suffix_002, kindSupport6_suffix_003, kindSupport6_suffix_004, kindSupport6_suffix_005, kindSupport6_suffix_006, kindSupport6_suffix_007, kindSupport6_suffix_008, kindSupport6_suffix_009, kindSupport6_suffix_010, kindSupport6_suffix_011, kindSupport6_suffix_012, kindSupport6_suffix_013, kindSupport6_suffix_014, kindSupport6_suffix_015, kindSupport6_suffix_016, kindSupport6_suffix_017, kindSupport6_suffix_018, kindSupport6_suffix_019, kindSupport6_suffix_020, kindSupport6_suffix_021, kindSupport6_suffix_022, kindSupport6_suffix_023, kindSupport6_suffix_024, kindSupport6_suffix_025, kindSupport6_suffix_026, kindSupport6_suffix_027, kindSupport6_suffix_028, kindSupport6_suffix_029, kindSupport6_suffix_030, kindSupport6_suffix_031, kindSupport6_suffix_032, kindSupport6_suffix_033, kindSupport6_suffix_034, kindSupport6_suffix_035, kindSupport6_suffix_036, kindSupport6_suffix_037, kindSupport6_suffix_038, kindSupport6_suffix_039, kindSupport6_suffix_040, kindSupport6_suffix_041, kindSupport6_suffix_042, kindSupport6_suffix_043, kindSupport6_suffix_044, kindSupport6_suffix_045, kindSupport6_suffix_046, kindSupport6_suffix_047, kindSupport6_suffix_048, kindSupport6_suffix_049, kindSupport6_suffix_050, kindSupport6_suffix_051, kindSupport6_suffix_052, kindSupport6_suffix_053, kindSupport6_suffix_054, kindSupport6_suffix_055, kindSupport6_suffix_056, kindSupport6_suffix_057, kindSupport6_suffix_058, kindSupport6_suffix_059, kindSupport6_suffix_060, kindSupport6_suffix_061, kindSupport6_suffix_062, kindSupport6_suffix_063, kindSupport6_suffix_064, kindSupport6_suffix_065, kindSupport6_suffix_066, kindSupport6_suffix_067, kindSupport6_suffix_068, kindSupport6_suffix_069, kindSupport6_suffix_070, kindSupport6_suffix_071, kindSupport6_suffix_072, kindSupport6_suffix_073, kindSupport6_suffix_074, kindSupport6_suffix_075, kindSupport6_suffix_076, kindSupport6_suffix_077, kindSupport6_suffix_078, kindSupport6_suffix_079, kindSupport6_suffix_080, kindSupport6_suffix_081, kindSupport6_suffix_082, kindSupport6_suffix_083, kindSupport6_suffix_084, kindSupport6_suffix_085, kindSupport6_suffix_086, kindSupport6_suffix_087, kindSupport6_suffix_088, kindSupport6_suffix_089, kindSupport6_suffix_090, kindSupport6_suffix_091, kindSupport6_suffix_092, kindSupport6_suffix_093, kindSupport6_suffix_094, kindSupport6_suffix_095, kindSupport6_suffix_096, kindSupport6_suffix_097, kindSupport6_suffix_098, kindSupport6_suffix_099, kindSupport6_suffix_100, kindSupport6_suffix_101, kindSupport6_suffix_102, kindSupport6_suffix_103, kindSupport6_suffix_104, kindSupport6_suffix_105, kindSupport6_suffix_106, kindSupport6_suffix_107, kindSupport6_suffix_108, kindSupport6_suffix_109, kindSupport6_suffix_110, kindSupport6_suffix_111, kindSupport6_suffix_112, kindSupport6_suffix_113, kindSupport6_suffix_114, kindSupport6_suffix_115, kindSupport6_suffix_116, kindSupport6_suffix_117, kindSupport6_suffix_118, kindSupport6_suffix_119, kindSupport6_suffix_120, kindSupport6_suffix_121, kindSupport6_suffix_122, kindSupport6_suffix_123, kindSupport6_suffix_124, kindSupport6_suffix_125, kindSupport6_suffix_126, kindSupport6_suffix_127, kindSupport6_suffix_128, kindSupport6_suffix_129, kindSupport6_suffix_130, kindSupport6_suffix_131, kindSupport6_suffix_132, kindSupport6_suffix_133, kindSupport6_suffix_134, kindSupport6_suffix_135, kindSupport6_suffix_136, kindSupport6_suffix_137, kindSupport6_suffix_138, kindSupport6_suffix_139, kindSupport6_suffix_140, kindSupport6_suffix_141, kindSupport6_suffix_142, kindSupport6_suffix_143, kindSupport6_suffix_144, kindSupport6_suffix_145, kindSupport6_suffix_146, kindSupport6_suffix_147, kindSupport6_suffix_148, kindSupport6_suffix_149, kindSupport6_suffix_150, kindSupport6_suffix_151, kindSupport6_suffix_152, kindSupport6_suffix_153, kindSupport6_suffix_154, kindSupport6_suffix_155, kindSupport6_suffix_156, kindSupport6_suffix_157, kindSupport6_suffix_158, kindSupport6_suffix_159, kindSupport6_suffix_160, kindSupport6_suffix_161, kindSupport6_suffix_162, List.all_append, List.all_nil, kindSupport6_000_checked, kindSupport6_001_checked, kindSupport6_002_checked, kindSupport6_003_checked, kindSupport6_004_checked, kindSupport6_005_checked, kindSupport6_006_checked, kindSupport6_007_checked, kindSupport6_008_checked, kindSupport6_009_checked, kindSupport6_010_checked, kindSupport6_011_checked, kindSupport6_012_checked, kindSupport6_013_checked, kindSupport6_014_checked, kindSupport6_015_checked, kindSupport6_016_checked, kindSupport6_017_checked, kindSupport6_018_checked, kindSupport6_019_checked, kindSupport6_020_checked, kindSupport6_021_checked, kindSupport6_022_checked, kindSupport6_023_checked, kindSupport6_024_checked, kindSupport6_025_checked, kindSupport6_026_checked, kindSupport6_027_checked, kindSupport6_028_checked, kindSupport6_029_checked, kindSupport6_030_checked, kindSupport6_031_checked, kindSupport6_032_checked, kindSupport6_033_checked, kindSupport6_034_checked, kindSupport6_035_checked, kindSupport6_036_checked, kindSupport6_037_checked, kindSupport6_038_checked, kindSupport6_039_checked, kindSupport6_040_checked, kindSupport6_041_checked, kindSupport6_042_checked, kindSupport6_043_checked, kindSupport6_044_checked, kindSupport6_045_checked, kindSupport6_046_checked, kindSupport6_047_checked, kindSupport6_048_checked, kindSupport6_049_checked, kindSupport6_050_checked, kindSupport6_051_checked, kindSupport6_052_checked, kindSupport6_053_checked, kindSupport6_054_checked, kindSupport6_055_checked, kindSupport6_056_checked, kindSupport6_057_checked, kindSupport6_058_checked, kindSupport6_059_checked, kindSupport6_060_checked, kindSupport6_061_checked, kindSupport6_062_checked, kindSupport6_063_checked, kindSupport6_064_checked, kindSupport6_065_checked, kindSupport6_066_checked, kindSupport6_067_checked, kindSupport6_068_checked, kindSupport6_069_checked, kindSupport6_070_checked, kindSupport6_071_checked, kindSupport6_072_checked, kindSupport6_073_checked, kindSupport6_074_checked, kindSupport6_075_checked, kindSupport6_076_checked, kindSupport6_077_checked, kindSupport6_078_checked, kindSupport6_079_checked, kindSupport6_080_checked, kindSupport6_081_checked, kindSupport6_082_checked, kindSupport6_083_checked, kindSupport6_084_checked, kindSupport6_085_checked, kindSupport6_086_checked, kindSupport6_087_checked, kindSupport6_088_checked, kindSupport6_089_checked, kindSupport6_090_checked, kindSupport6_091_checked, kindSupport6_092_checked, kindSupport6_093_checked, kindSupport6_094_checked, kindSupport6_095_checked, kindSupport6_096_checked, kindSupport6_097_checked, kindSupport6_098_checked, kindSupport6_099_checked, kindSupport6_100_checked, kindSupport6_101_checked, kindSupport6_102_checked, kindSupport6_103_checked, kindSupport6_104_checked, kindSupport6_105_checked, kindSupport6_106_checked, kindSupport6_107_checked, kindSupport6_108_checked, kindSupport6_109_checked, kindSupport6_110_checked, kindSupport6_111_checked, kindSupport6_112_checked, kindSupport6_113_checked, kindSupport6_114_checked, kindSupport6_115_checked, kindSupport6_116_checked, kindSupport6_117_checked, kindSupport6_118_checked, kindSupport6_119_checked, kindSupport6_120_checked, kindSupport6_121_checked, kindSupport6_122_checked, kindSupport6_123_checked, kindSupport6_124_checked, kindSupport6_125_checked, kindSupport6_126_checked, kindSupport6_127_checked, kindSupport6_128_checked, kindSupport6_129_checked, kindSupport6_130_checked, kindSupport6_131_checked, kindSupport6_132_checked, kindSupport6_133_checked, kindSupport6_134_checked, kindSupport6_135_checked, kindSupport6_136_checked, kindSupport6_137_checked, kindSupport6_138_checked, kindSupport6_139_checked, kindSupport6_140_checked, kindSupport6_141_checked, kindSupport6_142_checked, kindSupport6_143_checked, kindSupport6_144_checked, kindSupport6_145_checked, kindSupport6_146_checked, kindSupport6_147_checked, kindSupport6_148_checked, kindSupport6_149_checked, kindSupport6_150_checked, kindSupport6_151_checked, kindSupport6_152_checked, kindSupport6_153_checked, kindSupport6_154_checked, kindSupport6_155_checked, kindSupport6_156_checked, kindSupport6_157_checked, kindSupport6_158_checked, kindSupport6_159_checked, kindSupport6_160_checked, kindSupport6_161_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
