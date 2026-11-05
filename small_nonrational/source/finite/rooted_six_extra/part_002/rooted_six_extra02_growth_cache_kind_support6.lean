module
prelude
public import BundledChecks.RootedSixExtra02GrowthCacheKindSupport6Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport6_suffix_decode_117 : PackedRawNatGrowth.readList 13 0 kindSupport6_rest_117 =
    (kindSupport6_suffix_117, kindSupport6_rest_117) := by rfl
theorem kindSupport6_suffix_decode_116 : PackedRawNatGrowth.readList 13 32 kindSupport6_rest_116 =
    (kindSupport6_suffix_116, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 0
    kindSupport6_rest_116 kindSupport6_rest_117 kindSupport6_rest_117
    kindSupport6_116 kindSupport6_suffix_117 kindSupport6_116_decode kindSupport6_suffix_decode_117
theorem kindSupport6_suffix_decode_115 : PackedRawNatGrowth.readList 13 64 kindSupport6_rest_115 =
    (kindSupport6_suffix_115, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 32
    kindSupport6_rest_115 kindSupport6_rest_116 kindSupport6_rest_117
    kindSupport6_115 kindSupport6_suffix_116 kindSupport6_115_decode kindSupport6_suffix_decode_116
theorem kindSupport6_suffix_decode_114 : PackedRawNatGrowth.readList 13 96 kindSupport6_rest_114 =
    (kindSupport6_suffix_114, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 64
    kindSupport6_rest_114 kindSupport6_rest_115 kindSupport6_rest_117
    kindSupport6_114 kindSupport6_suffix_115 kindSupport6_114_decode kindSupport6_suffix_decode_115
theorem kindSupport6_suffix_decode_113 : PackedRawNatGrowth.readList 13 128 kindSupport6_rest_113 =
    (kindSupport6_suffix_113, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 96
    kindSupport6_rest_113 kindSupport6_rest_114 kindSupport6_rest_117
    kindSupport6_113 kindSupport6_suffix_114 kindSupport6_113_decode kindSupport6_suffix_decode_114
theorem kindSupport6_suffix_decode_112 : PackedRawNatGrowth.readList 13 160 kindSupport6_rest_112 =
    (kindSupport6_suffix_112, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 128
    kindSupport6_rest_112 kindSupport6_rest_113 kindSupport6_rest_117
    kindSupport6_112 kindSupport6_suffix_113 kindSupport6_112_decode kindSupport6_suffix_decode_113
theorem kindSupport6_suffix_decode_111 : PackedRawNatGrowth.readList 13 192 kindSupport6_rest_111 =
    (kindSupport6_suffix_111, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 160
    kindSupport6_rest_111 kindSupport6_rest_112 kindSupport6_rest_117
    kindSupport6_111 kindSupport6_suffix_112 kindSupport6_111_decode kindSupport6_suffix_decode_112
theorem kindSupport6_suffix_decode_110 : PackedRawNatGrowth.readList 13 224 kindSupport6_rest_110 =
    (kindSupport6_suffix_110, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 192
    kindSupport6_rest_110 kindSupport6_rest_111 kindSupport6_rest_117
    kindSupport6_110 kindSupport6_suffix_111 kindSupport6_110_decode kindSupport6_suffix_decode_111
theorem kindSupport6_suffix_decode_109 : PackedRawNatGrowth.readList 13 256 kindSupport6_rest_109 =
    (kindSupport6_suffix_109, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 224
    kindSupport6_rest_109 kindSupport6_rest_110 kindSupport6_rest_117
    kindSupport6_109 kindSupport6_suffix_110 kindSupport6_109_decode kindSupport6_suffix_decode_110
theorem kindSupport6_suffix_decode_108 : PackedRawNatGrowth.readList 13 288 kindSupport6_rest_108 =
    (kindSupport6_suffix_108, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 256
    kindSupport6_rest_108 kindSupport6_rest_109 kindSupport6_rest_117
    kindSupport6_108 kindSupport6_suffix_109 kindSupport6_108_decode kindSupport6_suffix_decode_109
theorem kindSupport6_suffix_decode_107 : PackedRawNatGrowth.readList 13 320 kindSupport6_rest_107 =
    (kindSupport6_suffix_107, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 288
    kindSupport6_rest_107 kindSupport6_rest_108 kindSupport6_rest_117
    kindSupport6_107 kindSupport6_suffix_108 kindSupport6_107_decode kindSupport6_suffix_decode_108
theorem kindSupport6_suffix_decode_106 : PackedRawNatGrowth.readList 13 352 kindSupport6_rest_106 =
    (kindSupport6_suffix_106, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 320
    kindSupport6_rest_106 kindSupport6_rest_107 kindSupport6_rest_117
    kindSupport6_106 kindSupport6_suffix_107 kindSupport6_106_decode kindSupport6_suffix_decode_107
theorem kindSupport6_suffix_decode_105 : PackedRawNatGrowth.readList 13 384 kindSupport6_rest_105 =
    (kindSupport6_suffix_105, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 352
    kindSupport6_rest_105 kindSupport6_rest_106 kindSupport6_rest_117
    kindSupport6_105 kindSupport6_suffix_106 kindSupport6_105_decode kindSupport6_suffix_decode_106
theorem kindSupport6_suffix_decode_104 : PackedRawNatGrowth.readList 13 416 kindSupport6_rest_104 =
    (kindSupport6_suffix_104, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 384
    kindSupport6_rest_104 kindSupport6_rest_105 kindSupport6_rest_117
    kindSupport6_104 kindSupport6_suffix_105 kindSupport6_104_decode kindSupport6_suffix_decode_105
theorem kindSupport6_suffix_decode_103 : PackedRawNatGrowth.readList 13 448 kindSupport6_rest_103 =
    (kindSupport6_suffix_103, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 416
    kindSupport6_rest_103 kindSupport6_rest_104 kindSupport6_rest_117
    kindSupport6_103 kindSupport6_suffix_104 kindSupport6_103_decode kindSupport6_suffix_decode_104
theorem kindSupport6_suffix_decode_102 : PackedRawNatGrowth.readList 13 480 kindSupport6_rest_102 =
    (kindSupport6_suffix_102, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 448
    kindSupport6_rest_102 kindSupport6_rest_103 kindSupport6_rest_117
    kindSupport6_102 kindSupport6_suffix_103 kindSupport6_102_decode kindSupport6_suffix_decode_103
theorem kindSupport6_suffix_decode_101 : PackedRawNatGrowth.readList 13 512 kindSupport6_rest_101 =
    (kindSupport6_suffix_101, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 480
    kindSupport6_rest_101 kindSupport6_rest_102 kindSupport6_rest_117
    kindSupport6_101 kindSupport6_suffix_102 kindSupport6_101_decode kindSupport6_suffix_decode_102
theorem kindSupport6_suffix_decode_100 : PackedRawNatGrowth.readList 13 544 kindSupport6_rest_100 =
    (kindSupport6_suffix_100, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 512
    kindSupport6_rest_100 kindSupport6_rest_101 kindSupport6_rest_117
    kindSupport6_100 kindSupport6_suffix_101 kindSupport6_100_decode kindSupport6_suffix_decode_101
theorem kindSupport6_suffix_decode_099 : PackedRawNatGrowth.readList 13 576 kindSupport6_rest_099 =
    (kindSupport6_suffix_099, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 544
    kindSupport6_rest_099 kindSupport6_rest_100 kindSupport6_rest_117
    kindSupport6_099 kindSupport6_suffix_100 kindSupport6_099_decode kindSupport6_suffix_decode_100
theorem kindSupport6_suffix_decode_098 : PackedRawNatGrowth.readList 13 608 kindSupport6_rest_098 =
    (kindSupport6_suffix_098, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 576
    kindSupport6_rest_098 kindSupport6_rest_099 kindSupport6_rest_117
    kindSupport6_098 kindSupport6_suffix_099 kindSupport6_098_decode kindSupport6_suffix_decode_099
theorem kindSupport6_suffix_decode_097 : PackedRawNatGrowth.readList 13 640 kindSupport6_rest_097 =
    (kindSupport6_suffix_097, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 608
    kindSupport6_rest_097 kindSupport6_rest_098 kindSupport6_rest_117
    kindSupport6_097 kindSupport6_suffix_098 kindSupport6_097_decode kindSupport6_suffix_decode_098
theorem kindSupport6_suffix_decode_096 : PackedRawNatGrowth.readList 13 672 kindSupport6_rest_096 =
    (kindSupport6_suffix_096, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 640
    kindSupport6_rest_096 kindSupport6_rest_097 kindSupport6_rest_117
    kindSupport6_096 kindSupport6_suffix_097 kindSupport6_096_decode kindSupport6_suffix_decode_097
theorem kindSupport6_suffix_decode_095 : PackedRawNatGrowth.readList 13 704 kindSupport6_rest_095 =
    (kindSupport6_suffix_095, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 672
    kindSupport6_rest_095 kindSupport6_rest_096 kindSupport6_rest_117
    kindSupport6_095 kindSupport6_suffix_096 kindSupport6_095_decode kindSupport6_suffix_decode_096
theorem kindSupport6_suffix_decode_094 : PackedRawNatGrowth.readList 13 736 kindSupport6_rest_094 =
    (kindSupport6_suffix_094, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 704
    kindSupport6_rest_094 kindSupport6_rest_095 kindSupport6_rest_117
    kindSupport6_094 kindSupport6_suffix_095 kindSupport6_094_decode kindSupport6_suffix_decode_095
theorem kindSupport6_suffix_decode_093 : PackedRawNatGrowth.readList 13 768 kindSupport6_rest_093 =
    (kindSupport6_suffix_093, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 736
    kindSupport6_rest_093 kindSupport6_rest_094 kindSupport6_rest_117
    kindSupport6_093 kindSupport6_suffix_094 kindSupport6_093_decode kindSupport6_suffix_decode_094
theorem kindSupport6_suffix_decode_092 : PackedRawNatGrowth.readList 13 800 kindSupport6_rest_092 =
    (kindSupport6_suffix_092, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 768
    kindSupport6_rest_092 kindSupport6_rest_093 kindSupport6_rest_117
    kindSupport6_092 kindSupport6_suffix_093 kindSupport6_092_decode kindSupport6_suffix_decode_093
theorem kindSupport6_suffix_decode_091 : PackedRawNatGrowth.readList 13 832 kindSupport6_rest_091 =
    (kindSupport6_suffix_091, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 800
    kindSupport6_rest_091 kindSupport6_rest_092 kindSupport6_rest_117
    kindSupport6_091 kindSupport6_suffix_092 kindSupport6_091_decode kindSupport6_suffix_decode_092
theorem kindSupport6_suffix_decode_090 : PackedRawNatGrowth.readList 13 864 kindSupport6_rest_090 =
    (kindSupport6_suffix_090, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 832
    kindSupport6_rest_090 kindSupport6_rest_091 kindSupport6_rest_117
    kindSupport6_090 kindSupport6_suffix_091 kindSupport6_090_decode kindSupport6_suffix_decode_091
theorem kindSupport6_suffix_decode_089 : PackedRawNatGrowth.readList 13 896 kindSupport6_rest_089 =
    (kindSupport6_suffix_089, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 864
    kindSupport6_rest_089 kindSupport6_rest_090 kindSupport6_rest_117
    kindSupport6_089 kindSupport6_suffix_090 kindSupport6_089_decode kindSupport6_suffix_decode_090
theorem kindSupport6_suffix_decode_088 : PackedRawNatGrowth.readList 13 928 kindSupport6_rest_088 =
    (kindSupport6_suffix_088, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 896
    kindSupport6_rest_088 kindSupport6_rest_089 kindSupport6_rest_117
    kindSupport6_088 kindSupport6_suffix_089 kindSupport6_088_decode kindSupport6_suffix_decode_089
theorem kindSupport6_suffix_decode_087 : PackedRawNatGrowth.readList 13 960 kindSupport6_rest_087 =
    (kindSupport6_suffix_087, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 928
    kindSupport6_rest_087 kindSupport6_rest_088 kindSupport6_rest_117
    kindSupport6_087 kindSupport6_suffix_088 kindSupport6_087_decode kindSupport6_suffix_decode_088
theorem kindSupport6_suffix_decode_086 : PackedRawNatGrowth.readList 13 992 kindSupport6_rest_086 =
    (kindSupport6_suffix_086, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 960
    kindSupport6_rest_086 kindSupport6_rest_087 kindSupport6_rest_117
    kindSupport6_086 kindSupport6_suffix_087 kindSupport6_086_decode kindSupport6_suffix_decode_087
theorem kindSupport6_suffix_decode_085 : PackedRawNatGrowth.readList 13 1024 kindSupport6_rest_085 =
    (kindSupport6_suffix_085, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 992
    kindSupport6_rest_085 kindSupport6_rest_086 kindSupport6_rest_117
    kindSupport6_085 kindSupport6_suffix_086 kindSupport6_085_decode kindSupport6_suffix_decode_086
theorem kindSupport6_suffix_decode_084 : PackedRawNatGrowth.readList 13 1056 kindSupport6_rest_084 =
    (kindSupport6_suffix_084, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1024
    kindSupport6_rest_084 kindSupport6_rest_085 kindSupport6_rest_117
    kindSupport6_084 kindSupport6_suffix_085 kindSupport6_084_decode kindSupport6_suffix_decode_085
theorem kindSupport6_suffix_decode_083 : PackedRawNatGrowth.readList 13 1088 kindSupport6_rest_083 =
    (kindSupport6_suffix_083, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1056
    kindSupport6_rest_083 kindSupport6_rest_084 kindSupport6_rest_117
    kindSupport6_083 kindSupport6_suffix_084 kindSupport6_083_decode kindSupport6_suffix_decode_084
theorem kindSupport6_suffix_decode_082 : PackedRawNatGrowth.readList 13 1120 kindSupport6_rest_082 =
    (kindSupport6_suffix_082, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1088
    kindSupport6_rest_082 kindSupport6_rest_083 kindSupport6_rest_117
    kindSupport6_082 kindSupport6_suffix_083 kindSupport6_082_decode kindSupport6_suffix_decode_083
theorem kindSupport6_suffix_decode_081 : PackedRawNatGrowth.readList 13 1152 kindSupport6_rest_081 =
    (kindSupport6_suffix_081, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1120
    kindSupport6_rest_081 kindSupport6_rest_082 kindSupport6_rest_117
    kindSupport6_081 kindSupport6_suffix_082 kindSupport6_081_decode kindSupport6_suffix_decode_082
theorem kindSupport6_suffix_decode_080 : PackedRawNatGrowth.readList 13 1184 kindSupport6_rest_080 =
    (kindSupport6_suffix_080, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1152
    kindSupport6_rest_080 kindSupport6_rest_081 kindSupport6_rest_117
    kindSupport6_080 kindSupport6_suffix_081 kindSupport6_080_decode kindSupport6_suffix_decode_081
theorem kindSupport6_suffix_decode_079 : PackedRawNatGrowth.readList 13 1216 kindSupport6_rest_079 =
    (kindSupport6_suffix_079, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1184
    kindSupport6_rest_079 kindSupport6_rest_080 kindSupport6_rest_117
    kindSupport6_079 kindSupport6_suffix_080 kindSupport6_079_decode kindSupport6_suffix_decode_080
theorem kindSupport6_suffix_decode_078 : PackedRawNatGrowth.readList 13 1248 kindSupport6_rest_078 =
    (kindSupport6_suffix_078, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1216
    kindSupport6_rest_078 kindSupport6_rest_079 kindSupport6_rest_117
    kindSupport6_078 kindSupport6_suffix_079 kindSupport6_078_decode kindSupport6_suffix_decode_079
theorem kindSupport6_suffix_decode_077 : PackedRawNatGrowth.readList 13 1280 kindSupport6_rest_077 =
    (kindSupport6_suffix_077, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1248
    kindSupport6_rest_077 kindSupport6_rest_078 kindSupport6_rest_117
    kindSupport6_077 kindSupport6_suffix_078 kindSupport6_077_decode kindSupport6_suffix_decode_078
theorem kindSupport6_suffix_decode_076 : PackedRawNatGrowth.readList 13 1312 kindSupport6_rest_076 =
    (kindSupport6_suffix_076, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1280
    kindSupport6_rest_076 kindSupport6_rest_077 kindSupport6_rest_117
    kindSupport6_076 kindSupport6_suffix_077 kindSupport6_076_decode kindSupport6_suffix_decode_077
theorem kindSupport6_suffix_decode_075 : PackedRawNatGrowth.readList 13 1344 kindSupport6_rest_075 =
    (kindSupport6_suffix_075, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1312
    kindSupport6_rest_075 kindSupport6_rest_076 kindSupport6_rest_117
    kindSupport6_075 kindSupport6_suffix_076 kindSupport6_075_decode kindSupport6_suffix_decode_076
theorem kindSupport6_suffix_decode_074 : PackedRawNatGrowth.readList 13 1376 kindSupport6_rest_074 =
    (kindSupport6_suffix_074, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1344
    kindSupport6_rest_074 kindSupport6_rest_075 kindSupport6_rest_117
    kindSupport6_074 kindSupport6_suffix_075 kindSupport6_074_decode kindSupport6_suffix_decode_075
theorem kindSupport6_suffix_decode_073 : PackedRawNatGrowth.readList 13 1408 kindSupport6_rest_073 =
    (kindSupport6_suffix_073, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1376
    kindSupport6_rest_073 kindSupport6_rest_074 kindSupport6_rest_117
    kindSupport6_073 kindSupport6_suffix_074 kindSupport6_073_decode kindSupport6_suffix_decode_074
theorem kindSupport6_suffix_decode_072 : PackedRawNatGrowth.readList 13 1440 kindSupport6_rest_072 =
    (kindSupport6_suffix_072, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1408
    kindSupport6_rest_072 kindSupport6_rest_073 kindSupport6_rest_117
    kindSupport6_072 kindSupport6_suffix_073 kindSupport6_072_decode kindSupport6_suffix_decode_073
theorem kindSupport6_suffix_decode_071 : PackedRawNatGrowth.readList 13 1472 kindSupport6_rest_071 =
    (kindSupport6_suffix_071, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1440
    kindSupport6_rest_071 kindSupport6_rest_072 kindSupport6_rest_117
    kindSupport6_071 kindSupport6_suffix_072 kindSupport6_071_decode kindSupport6_suffix_decode_072
theorem kindSupport6_suffix_decode_070 : PackedRawNatGrowth.readList 13 1504 kindSupport6_rest_070 =
    (kindSupport6_suffix_070, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1472
    kindSupport6_rest_070 kindSupport6_rest_071 kindSupport6_rest_117
    kindSupport6_070 kindSupport6_suffix_071 kindSupport6_070_decode kindSupport6_suffix_decode_071
theorem kindSupport6_suffix_decode_069 : PackedRawNatGrowth.readList 13 1536 kindSupport6_rest_069 =
    (kindSupport6_suffix_069, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1504
    kindSupport6_rest_069 kindSupport6_rest_070 kindSupport6_rest_117
    kindSupport6_069 kindSupport6_suffix_070 kindSupport6_069_decode kindSupport6_suffix_decode_070
theorem kindSupport6_suffix_decode_068 : PackedRawNatGrowth.readList 13 1568 kindSupport6_rest_068 =
    (kindSupport6_suffix_068, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1536
    kindSupport6_rest_068 kindSupport6_rest_069 kindSupport6_rest_117
    kindSupport6_068 kindSupport6_suffix_069 kindSupport6_068_decode kindSupport6_suffix_decode_069
theorem kindSupport6_suffix_decode_067 : PackedRawNatGrowth.readList 13 1600 kindSupport6_rest_067 =
    (kindSupport6_suffix_067, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1568
    kindSupport6_rest_067 kindSupport6_rest_068 kindSupport6_rest_117
    kindSupport6_067 kindSupport6_suffix_068 kindSupport6_067_decode kindSupport6_suffix_decode_068
theorem kindSupport6_suffix_decode_066 : PackedRawNatGrowth.readList 13 1632 kindSupport6_rest_066 =
    (kindSupport6_suffix_066, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1600
    kindSupport6_rest_066 kindSupport6_rest_067 kindSupport6_rest_117
    kindSupport6_066 kindSupport6_suffix_067 kindSupport6_066_decode kindSupport6_suffix_decode_067
theorem kindSupport6_suffix_decode_065 : PackedRawNatGrowth.readList 13 1664 kindSupport6_rest_065 =
    (kindSupport6_suffix_065, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1632
    kindSupport6_rest_065 kindSupport6_rest_066 kindSupport6_rest_117
    kindSupport6_065 kindSupport6_suffix_066 kindSupport6_065_decode kindSupport6_suffix_decode_066
theorem kindSupport6_suffix_decode_064 : PackedRawNatGrowth.readList 13 1696 kindSupport6_rest_064 =
    (kindSupport6_suffix_064, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1664
    kindSupport6_rest_064 kindSupport6_rest_065 kindSupport6_rest_117
    kindSupport6_064 kindSupport6_suffix_065 kindSupport6_064_decode kindSupport6_suffix_decode_065
theorem kindSupport6_suffix_decode_063 : PackedRawNatGrowth.readList 13 1728 kindSupport6_rest_063 =
    (kindSupport6_suffix_063, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1696
    kindSupport6_rest_063 kindSupport6_rest_064 kindSupport6_rest_117
    kindSupport6_063 kindSupport6_suffix_064 kindSupport6_063_decode kindSupport6_suffix_decode_064
theorem kindSupport6_suffix_decode_062 : PackedRawNatGrowth.readList 13 1760 kindSupport6_rest_062 =
    (kindSupport6_suffix_062, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1728
    kindSupport6_rest_062 kindSupport6_rest_063 kindSupport6_rest_117
    kindSupport6_062 kindSupport6_suffix_063 kindSupport6_062_decode kindSupport6_suffix_decode_063
theorem kindSupport6_suffix_decode_061 : PackedRawNatGrowth.readList 13 1792 kindSupport6_rest_061 =
    (kindSupport6_suffix_061, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1760
    kindSupport6_rest_061 kindSupport6_rest_062 kindSupport6_rest_117
    kindSupport6_061 kindSupport6_suffix_062 kindSupport6_061_decode kindSupport6_suffix_decode_062
theorem kindSupport6_suffix_decode_060 : PackedRawNatGrowth.readList 13 1824 kindSupport6_rest_060 =
    (kindSupport6_suffix_060, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1792
    kindSupport6_rest_060 kindSupport6_rest_061 kindSupport6_rest_117
    kindSupport6_060 kindSupport6_suffix_061 kindSupport6_060_decode kindSupport6_suffix_decode_061
theorem kindSupport6_suffix_decode_059 : PackedRawNatGrowth.readList 13 1856 kindSupport6_rest_059 =
    (kindSupport6_suffix_059, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1824
    kindSupport6_rest_059 kindSupport6_rest_060 kindSupport6_rest_117
    kindSupport6_059 kindSupport6_suffix_060 kindSupport6_059_decode kindSupport6_suffix_decode_060
theorem kindSupport6_suffix_decode_058 : PackedRawNatGrowth.readList 13 1888 kindSupport6_rest_058 =
    (kindSupport6_suffix_058, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1856
    kindSupport6_rest_058 kindSupport6_rest_059 kindSupport6_rest_117
    kindSupport6_058 kindSupport6_suffix_059 kindSupport6_058_decode kindSupport6_suffix_decode_059
theorem kindSupport6_suffix_decode_057 : PackedRawNatGrowth.readList 13 1920 kindSupport6_rest_057 =
    (kindSupport6_suffix_057, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1888
    kindSupport6_rest_057 kindSupport6_rest_058 kindSupport6_rest_117
    kindSupport6_057 kindSupport6_suffix_058 kindSupport6_057_decode kindSupport6_suffix_decode_058
theorem kindSupport6_suffix_decode_056 : PackedRawNatGrowth.readList 13 1952 kindSupport6_rest_056 =
    (kindSupport6_suffix_056, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1920
    kindSupport6_rest_056 kindSupport6_rest_057 kindSupport6_rest_117
    kindSupport6_056 kindSupport6_suffix_057 kindSupport6_056_decode kindSupport6_suffix_decode_057
theorem kindSupport6_suffix_decode_055 : PackedRawNatGrowth.readList 13 1984 kindSupport6_rest_055 =
    (kindSupport6_suffix_055, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1952
    kindSupport6_rest_055 kindSupport6_rest_056 kindSupport6_rest_117
    kindSupport6_055 kindSupport6_suffix_056 kindSupport6_055_decode kindSupport6_suffix_decode_056
theorem kindSupport6_suffix_decode_054 : PackedRawNatGrowth.readList 13 2016 kindSupport6_rest_054 =
    (kindSupport6_suffix_054, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 1984
    kindSupport6_rest_054 kindSupport6_rest_055 kindSupport6_rest_117
    kindSupport6_054 kindSupport6_suffix_055 kindSupport6_054_decode kindSupport6_suffix_decode_055
theorem kindSupport6_suffix_decode_053 : PackedRawNatGrowth.readList 13 2048 kindSupport6_rest_053 =
    (kindSupport6_suffix_053, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2016
    kindSupport6_rest_053 kindSupport6_rest_054 kindSupport6_rest_117
    kindSupport6_053 kindSupport6_suffix_054 kindSupport6_053_decode kindSupport6_suffix_decode_054
theorem kindSupport6_suffix_decode_052 : PackedRawNatGrowth.readList 13 2080 kindSupport6_rest_052 =
    (kindSupport6_suffix_052, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2048
    kindSupport6_rest_052 kindSupport6_rest_053 kindSupport6_rest_117
    kindSupport6_052 kindSupport6_suffix_053 kindSupport6_052_decode kindSupport6_suffix_decode_053
theorem kindSupport6_suffix_decode_051 : PackedRawNatGrowth.readList 13 2112 kindSupport6_rest_051 =
    (kindSupport6_suffix_051, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2080
    kindSupport6_rest_051 kindSupport6_rest_052 kindSupport6_rest_117
    kindSupport6_051 kindSupport6_suffix_052 kindSupport6_051_decode kindSupport6_suffix_decode_052
theorem kindSupport6_suffix_decode_050 : PackedRawNatGrowth.readList 13 2144 kindSupport6_rest_050 =
    (kindSupport6_suffix_050, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2112
    kindSupport6_rest_050 kindSupport6_rest_051 kindSupport6_rest_117
    kindSupport6_050 kindSupport6_suffix_051 kindSupport6_050_decode kindSupport6_suffix_decode_051
theorem kindSupport6_suffix_decode_049 : PackedRawNatGrowth.readList 13 2176 kindSupport6_rest_049 =
    (kindSupport6_suffix_049, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2144
    kindSupport6_rest_049 kindSupport6_rest_050 kindSupport6_rest_117
    kindSupport6_049 kindSupport6_suffix_050 kindSupport6_049_decode kindSupport6_suffix_decode_050
theorem kindSupport6_suffix_decode_048 : PackedRawNatGrowth.readList 13 2208 kindSupport6_rest_048 =
    (kindSupport6_suffix_048, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2176
    kindSupport6_rest_048 kindSupport6_rest_049 kindSupport6_rest_117
    kindSupport6_048 kindSupport6_suffix_049 kindSupport6_048_decode kindSupport6_suffix_decode_049
theorem kindSupport6_suffix_decode_047 : PackedRawNatGrowth.readList 13 2240 kindSupport6_rest_047 =
    (kindSupport6_suffix_047, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2208
    kindSupport6_rest_047 kindSupport6_rest_048 kindSupport6_rest_117
    kindSupport6_047 kindSupport6_suffix_048 kindSupport6_047_decode kindSupport6_suffix_decode_048
theorem kindSupport6_suffix_decode_046 : PackedRawNatGrowth.readList 13 2272 kindSupport6_rest_046 =
    (kindSupport6_suffix_046, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2240
    kindSupport6_rest_046 kindSupport6_rest_047 kindSupport6_rest_117
    kindSupport6_046 kindSupport6_suffix_047 kindSupport6_046_decode kindSupport6_suffix_decode_047
theorem kindSupport6_suffix_decode_045 : PackedRawNatGrowth.readList 13 2304 kindSupport6_rest_045 =
    (kindSupport6_suffix_045, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2272
    kindSupport6_rest_045 kindSupport6_rest_046 kindSupport6_rest_117
    kindSupport6_045 kindSupport6_suffix_046 kindSupport6_045_decode kindSupport6_suffix_decode_046
theorem kindSupport6_suffix_decode_044 : PackedRawNatGrowth.readList 13 2336 kindSupport6_rest_044 =
    (kindSupport6_suffix_044, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2304
    kindSupport6_rest_044 kindSupport6_rest_045 kindSupport6_rest_117
    kindSupport6_044 kindSupport6_suffix_045 kindSupport6_044_decode kindSupport6_suffix_decode_045
theorem kindSupport6_suffix_decode_043 : PackedRawNatGrowth.readList 13 2368 kindSupport6_rest_043 =
    (kindSupport6_suffix_043, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2336
    kindSupport6_rest_043 kindSupport6_rest_044 kindSupport6_rest_117
    kindSupport6_043 kindSupport6_suffix_044 kindSupport6_043_decode kindSupport6_suffix_decode_044
theorem kindSupport6_suffix_decode_042 : PackedRawNatGrowth.readList 13 2400 kindSupport6_rest_042 =
    (kindSupport6_suffix_042, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2368
    kindSupport6_rest_042 kindSupport6_rest_043 kindSupport6_rest_117
    kindSupport6_042 kindSupport6_suffix_043 kindSupport6_042_decode kindSupport6_suffix_decode_043
theorem kindSupport6_suffix_decode_041 : PackedRawNatGrowth.readList 13 2432 kindSupport6_rest_041 =
    (kindSupport6_suffix_041, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2400
    kindSupport6_rest_041 kindSupport6_rest_042 kindSupport6_rest_117
    kindSupport6_041 kindSupport6_suffix_042 kindSupport6_041_decode kindSupport6_suffix_decode_042
theorem kindSupport6_suffix_decode_040 : PackedRawNatGrowth.readList 13 2464 kindSupport6_rest_040 =
    (kindSupport6_suffix_040, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2432
    kindSupport6_rest_040 kindSupport6_rest_041 kindSupport6_rest_117
    kindSupport6_040 kindSupport6_suffix_041 kindSupport6_040_decode kindSupport6_suffix_decode_041
theorem kindSupport6_suffix_decode_039 : PackedRawNatGrowth.readList 13 2496 kindSupport6_rest_039 =
    (kindSupport6_suffix_039, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2464
    kindSupport6_rest_039 kindSupport6_rest_040 kindSupport6_rest_117
    kindSupport6_039 kindSupport6_suffix_040 kindSupport6_039_decode kindSupport6_suffix_decode_040
theorem kindSupport6_suffix_decode_038 : PackedRawNatGrowth.readList 13 2528 kindSupport6_rest_038 =
    (kindSupport6_suffix_038, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2496
    kindSupport6_rest_038 kindSupport6_rest_039 kindSupport6_rest_117
    kindSupport6_038 kindSupport6_suffix_039 kindSupport6_038_decode kindSupport6_suffix_decode_039
theorem kindSupport6_suffix_decode_037 : PackedRawNatGrowth.readList 13 2560 kindSupport6_rest_037 =
    (kindSupport6_suffix_037, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2528
    kindSupport6_rest_037 kindSupport6_rest_038 kindSupport6_rest_117
    kindSupport6_037 kindSupport6_suffix_038 kindSupport6_037_decode kindSupport6_suffix_decode_038
theorem kindSupport6_suffix_decode_036 : PackedRawNatGrowth.readList 13 2592 kindSupport6_rest_036 =
    (kindSupport6_suffix_036, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2560
    kindSupport6_rest_036 kindSupport6_rest_037 kindSupport6_rest_117
    kindSupport6_036 kindSupport6_suffix_037 kindSupport6_036_decode kindSupport6_suffix_decode_037
theorem kindSupport6_suffix_decode_035 : PackedRawNatGrowth.readList 13 2624 kindSupport6_rest_035 =
    (kindSupport6_suffix_035, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2592
    kindSupport6_rest_035 kindSupport6_rest_036 kindSupport6_rest_117
    kindSupport6_035 kindSupport6_suffix_036 kindSupport6_035_decode kindSupport6_suffix_decode_036
theorem kindSupport6_suffix_decode_034 : PackedRawNatGrowth.readList 13 2656 kindSupport6_rest_034 =
    (kindSupport6_suffix_034, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2624
    kindSupport6_rest_034 kindSupport6_rest_035 kindSupport6_rest_117
    kindSupport6_034 kindSupport6_suffix_035 kindSupport6_034_decode kindSupport6_suffix_decode_035
theorem kindSupport6_suffix_decode_033 : PackedRawNatGrowth.readList 13 2688 kindSupport6_rest_033 =
    (kindSupport6_suffix_033, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2656
    kindSupport6_rest_033 kindSupport6_rest_034 kindSupport6_rest_117
    kindSupport6_033 kindSupport6_suffix_034 kindSupport6_033_decode kindSupport6_suffix_decode_034
theorem kindSupport6_suffix_decode_032 : PackedRawNatGrowth.readList 13 2720 kindSupport6_rest_032 =
    (kindSupport6_suffix_032, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2688
    kindSupport6_rest_032 kindSupport6_rest_033 kindSupport6_rest_117
    kindSupport6_032 kindSupport6_suffix_033 kindSupport6_032_decode kindSupport6_suffix_decode_033
theorem kindSupport6_suffix_decode_031 : PackedRawNatGrowth.readList 13 2752 kindSupport6_rest_031 =
    (kindSupport6_suffix_031, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2720
    kindSupport6_rest_031 kindSupport6_rest_032 kindSupport6_rest_117
    kindSupport6_031 kindSupport6_suffix_032 kindSupport6_031_decode kindSupport6_suffix_decode_032
theorem kindSupport6_suffix_decode_030 : PackedRawNatGrowth.readList 13 2784 kindSupport6_rest_030 =
    (kindSupport6_suffix_030, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2752
    kindSupport6_rest_030 kindSupport6_rest_031 kindSupport6_rest_117
    kindSupport6_030 kindSupport6_suffix_031 kindSupport6_030_decode kindSupport6_suffix_decode_031
theorem kindSupport6_suffix_decode_029 : PackedRawNatGrowth.readList 13 2816 kindSupport6_rest_029 =
    (kindSupport6_suffix_029, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2784
    kindSupport6_rest_029 kindSupport6_rest_030 kindSupport6_rest_117
    kindSupport6_029 kindSupport6_suffix_030 kindSupport6_029_decode kindSupport6_suffix_decode_030
theorem kindSupport6_suffix_decode_028 : PackedRawNatGrowth.readList 13 2848 kindSupport6_rest_028 =
    (kindSupport6_suffix_028, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2816
    kindSupport6_rest_028 kindSupport6_rest_029 kindSupport6_rest_117
    kindSupport6_028 kindSupport6_suffix_029 kindSupport6_028_decode kindSupport6_suffix_decode_029
theorem kindSupport6_suffix_decode_027 : PackedRawNatGrowth.readList 13 2880 kindSupport6_rest_027 =
    (kindSupport6_suffix_027, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2848
    kindSupport6_rest_027 kindSupport6_rest_028 kindSupport6_rest_117
    kindSupport6_027 kindSupport6_suffix_028 kindSupport6_027_decode kindSupport6_suffix_decode_028
theorem kindSupport6_suffix_decode_026 : PackedRawNatGrowth.readList 13 2912 kindSupport6_rest_026 =
    (kindSupport6_suffix_026, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2880
    kindSupport6_rest_026 kindSupport6_rest_027 kindSupport6_rest_117
    kindSupport6_026 kindSupport6_suffix_027 kindSupport6_026_decode kindSupport6_suffix_decode_027
theorem kindSupport6_suffix_decode_025 : PackedRawNatGrowth.readList 13 2944 kindSupport6_rest_025 =
    (kindSupport6_suffix_025, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2912
    kindSupport6_rest_025 kindSupport6_rest_026 kindSupport6_rest_117
    kindSupport6_025 kindSupport6_suffix_026 kindSupport6_025_decode kindSupport6_suffix_decode_026
theorem kindSupport6_suffix_decode_024 : PackedRawNatGrowth.readList 13 2976 kindSupport6_rest_024 =
    (kindSupport6_suffix_024, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2944
    kindSupport6_rest_024 kindSupport6_rest_025 kindSupport6_rest_117
    kindSupport6_024 kindSupport6_suffix_025 kindSupport6_024_decode kindSupport6_suffix_decode_025
theorem kindSupport6_suffix_decode_023 : PackedRawNatGrowth.readList 13 3008 kindSupport6_rest_023 =
    (kindSupport6_suffix_023, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 2976
    kindSupport6_rest_023 kindSupport6_rest_024 kindSupport6_rest_117
    kindSupport6_023 kindSupport6_suffix_024 kindSupport6_023_decode kindSupport6_suffix_decode_024
theorem kindSupport6_suffix_decode_022 : PackedRawNatGrowth.readList 13 3040 kindSupport6_rest_022 =
    (kindSupport6_suffix_022, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3008
    kindSupport6_rest_022 kindSupport6_rest_023 kindSupport6_rest_117
    kindSupport6_022 kindSupport6_suffix_023 kindSupport6_022_decode kindSupport6_suffix_decode_023
theorem kindSupport6_suffix_decode_021 : PackedRawNatGrowth.readList 13 3072 kindSupport6_rest_021 =
    (kindSupport6_suffix_021, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3040
    kindSupport6_rest_021 kindSupport6_rest_022 kindSupport6_rest_117
    kindSupport6_021 kindSupport6_suffix_022 kindSupport6_021_decode kindSupport6_suffix_decode_022
theorem kindSupport6_suffix_decode_020 : PackedRawNatGrowth.readList 13 3104 kindSupport6_rest_020 =
    (kindSupport6_suffix_020, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3072
    kindSupport6_rest_020 kindSupport6_rest_021 kindSupport6_rest_117
    kindSupport6_020 kindSupport6_suffix_021 kindSupport6_020_decode kindSupport6_suffix_decode_021
theorem kindSupport6_suffix_decode_019 : PackedRawNatGrowth.readList 13 3136 kindSupport6_rest_019 =
    (kindSupport6_suffix_019, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3104
    kindSupport6_rest_019 kindSupport6_rest_020 kindSupport6_rest_117
    kindSupport6_019 kindSupport6_suffix_020 kindSupport6_019_decode kindSupport6_suffix_decode_020
theorem kindSupport6_suffix_decode_018 : PackedRawNatGrowth.readList 13 3168 kindSupport6_rest_018 =
    (kindSupport6_suffix_018, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3136
    kindSupport6_rest_018 kindSupport6_rest_019 kindSupport6_rest_117
    kindSupport6_018 kindSupport6_suffix_019 kindSupport6_018_decode kindSupport6_suffix_decode_019
theorem kindSupport6_suffix_decode_017 : PackedRawNatGrowth.readList 13 3200 kindSupport6_rest_017 =
    (kindSupport6_suffix_017, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3168
    kindSupport6_rest_017 kindSupport6_rest_018 kindSupport6_rest_117
    kindSupport6_017 kindSupport6_suffix_018 kindSupport6_017_decode kindSupport6_suffix_decode_018
theorem kindSupport6_suffix_decode_016 : PackedRawNatGrowth.readList 13 3232 kindSupport6_rest_016 =
    (kindSupport6_suffix_016, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3200
    kindSupport6_rest_016 kindSupport6_rest_017 kindSupport6_rest_117
    kindSupport6_016 kindSupport6_suffix_017 kindSupport6_016_decode kindSupport6_suffix_decode_017
theorem kindSupport6_suffix_decode_015 : PackedRawNatGrowth.readList 13 3264 kindSupport6_rest_015 =
    (kindSupport6_suffix_015, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3232
    kindSupport6_rest_015 kindSupport6_rest_016 kindSupport6_rest_117
    kindSupport6_015 kindSupport6_suffix_016 kindSupport6_015_decode kindSupport6_suffix_decode_016
theorem kindSupport6_suffix_decode_014 : PackedRawNatGrowth.readList 13 3296 kindSupport6_rest_014 =
    (kindSupport6_suffix_014, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3264
    kindSupport6_rest_014 kindSupport6_rest_015 kindSupport6_rest_117
    kindSupport6_014 kindSupport6_suffix_015 kindSupport6_014_decode kindSupport6_suffix_decode_015
theorem kindSupport6_suffix_decode_013 : PackedRawNatGrowth.readList 13 3328 kindSupport6_rest_013 =
    (kindSupport6_suffix_013, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3296
    kindSupport6_rest_013 kindSupport6_rest_014 kindSupport6_rest_117
    kindSupport6_013 kindSupport6_suffix_014 kindSupport6_013_decode kindSupport6_suffix_decode_014
theorem kindSupport6_suffix_decode_012 : PackedRawNatGrowth.readList 13 3360 kindSupport6_rest_012 =
    (kindSupport6_suffix_012, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3328
    kindSupport6_rest_012 kindSupport6_rest_013 kindSupport6_rest_117
    kindSupport6_012 kindSupport6_suffix_013 kindSupport6_012_decode kindSupport6_suffix_decode_013
theorem kindSupport6_suffix_decode_011 : PackedRawNatGrowth.readList 13 3392 kindSupport6_rest_011 =
    (kindSupport6_suffix_011, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3360
    kindSupport6_rest_011 kindSupport6_rest_012 kindSupport6_rest_117
    kindSupport6_011 kindSupport6_suffix_012 kindSupport6_011_decode kindSupport6_suffix_decode_012
theorem kindSupport6_suffix_decode_010 : PackedRawNatGrowth.readList 13 3424 kindSupport6_rest_010 =
    (kindSupport6_suffix_010, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3392
    kindSupport6_rest_010 kindSupport6_rest_011 kindSupport6_rest_117
    kindSupport6_010 kindSupport6_suffix_011 kindSupport6_010_decode kindSupport6_suffix_decode_011
theorem kindSupport6_suffix_decode_009 : PackedRawNatGrowth.readList 13 3456 kindSupport6_rest_009 =
    (kindSupport6_suffix_009, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3424
    kindSupport6_rest_009 kindSupport6_rest_010 kindSupport6_rest_117
    kindSupport6_009 kindSupport6_suffix_010 kindSupport6_009_decode kindSupport6_suffix_decode_010
theorem kindSupport6_suffix_decode_008 : PackedRawNatGrowth.readList 13 3488 kindSupport6_rest_008 =
    (kindSupport6_suffix_008, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3456
    kindSupport6_rest_008 kindSupport6_rest_009 kindSupport6_rest_117
    kindSupport6_008 kindSupport6_suffix_009 kindSupport6_008_decode kindSupport6_suffix_decode_009
theorem kindSupport6_suffix_decode_007 : PackedRawNatGrowth.readList 13 3520 kindSupport6_rest_007 =
    (kindSupport6_suffix_007, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3488
    kindSupport6_rest_007 kindSupport6_rest_008 kindSupport6_rest_117
    kindSupport6_007 kindSupport6_suffix_008 kindSupport6_007_decode kindSupport6_suffix_decode_008
theorem kindSupport6_suffix_decode_006 : PackedRawNatGrowth.readList 13 3552 kindSupport6_rest_006 =
    (kindSupport6_suffix_006, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3520
    kindSupport6_rest_006 kindSupport6_rest_007 kindSupport6_rest_117
    kindSupport6_006 kindSupport6_suffix_007 kindSupport6_006_decode kindSupport6_suffix_decode_007
theorem kindSupport6_suffix_decode_005 : PackedRawNatGrowth.readList 13 3584 kindSupport6_rest_005 =
    (kindSupport6_suffix_005, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3552
    kindSupport6_rest_005 kindSupport6_rest_006 kindSupport6_rest_117
    kindSupport6_005 kindSupport6_suffix_006 kindSupport6_005_decode kindSupport6_suffix_decode_006
theorem kindSupport6_suffix_decode_004 : PackedRawNatGrowth.readList 13 3616 kindSupport6_rest_004 =
    (kindSupport6_suffix_004, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3584
    kindSupport6_rest_004 kindSupport6_rest_005 kindSupport6_rest_117
    kindSupport6_004 kindSupport6_suffix_005 kindSupport6_004_decode kindSupport6_suffix_decode_005
theorem kindSupport6_suffix_decode_003 : PackedRawNatGrowth.readList 13 3648 kindSupport6_rest_003 =
    (kindSupport6_suffix_003, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3616
    kindSupport6_rest_003 kindSupport6_rest_004 kindSupport6_rest_117
    kindSupport6_003 kindSupport6_suffix_004 kindSupport6_003_decode kindSupport6_suffix_decode_004
theorem kindSupport6_suffix_decode_002 : PackedRawNatGrowth.readList 13 3680 kindSupport6_rest_002 =
    (kindSupport6_suffix_002, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3648
    kindSupport6_rest_002 kindSupport6_rest_003 kindSupport6_rest_117
    kindSupport6_002 kindSupport6_suffix_003 kindSupport6_002_decode kindSupport6_suffix_decode_003
theorem kindSupport6_suffix_decode_001 : PackedRawNatGrowth.readList 13 3712 kindSupport6_rest_001 =
    (kindSupport6_suffix_001, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3680
    kindSupport6_rest_001 kindSupport6_rest_002 kindSupport6_rest_117
    kindSupport6_001 kindSupport6_suffix_002 kindSupport6_001_decode kindSupport6_suffix_decode_002
theorem kindSupport6_suffix_decode_000 : PackedRawNatGrowth.readList 13 3744 kindSupport6_rest_000 =
    (kindSupport6_suffix_000, kindSupport6_rest_117) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3712
    kindSupport6_rest_000 kindSupport6_rest_001 kindSupport6_rest_117
    kindSupport6_000 kindSupport6_suffix_001 kindSupport6_000_decode kindSupport6_suffix_decode_001
theorem kindSupport6_eq : kindRows 6 = kindSupport6_suffix_000 := by
  change kindSupports 6 = kindSupport6_suffix_000
  rw [kindSupport6_source]
  exact congrArg Prod.fst kindSupport6_suffix_decode_000
theorem kindTest_large_6 : kindTest 6 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport6_eq]
    simp only [kindSupport6_suffix_000, kindSupport6_suffix_001, kindSupport6_suffix_002, kindSupport6_suffix_003, kindSupport6_suffix_004, kindSupport6_suffix_005, kindSupport6_suffix_006, kindSupport6_suffix_007, kindSupport6_suffix_008, kindSupport6_suffix_009, kindSupport6_suffix_010, kindSupport6_suffix_011, kindSupport6_suffix_012, kindSupport6_suffix_013, kindSupport6_suffix_014, kindSupport6_suffix_015, kindSupport6_suffix_016, kindSupport6_suffix_017, kindSupport6_suffix_018, kindSupport6_suffix_019, kindSupport6_suffix_020, kindSupport6_suffix_021, kindSupport6_suffix_022, kindSupport6_suffix_023, kindSupport6_suffix_024, kindSupport6_suffix_025, kindSupport6_suffix_026, kindSupport6_suffix_027, kindSupport6_suffix_028, kindSupport6_suffix_029, kindSupport6_suffix_030, kindSupport6_suffix_031, kindSupport6_suffix_032, kindSupport6_suffix_033, kindSupport6_suffix_034, kindSupport6_suffix_035, kindSupport6_suffix_036, kindSupport6_suffix_037, kindSupport6_suffix_038, kindSupport6_suffix_039, kindSupport6_suffix_040, kindSupport6_suffix_041, kindSupport6_suffix_042, kindSupport6_suffix_043, kindSupport6_suffix_044, kindSupport6_suffix_045, kindSupport6_suffix_046, kindSupport6_suffix_047, kindSupport6_suffix_048, kindSupport6_suffix_049, kindSupport6_suffix_050, kindSupport6_suffix_051, kindSupport6_suffix_052, kindSupport6_suffix_053, kindSupport6_suffix_054, kindSupport6_suffix_055, kindSupport6_suffix_056, kindSupport6_suffix_057, kindSupport6_suffix_058, kindSupport6_suffix_059, kindSupport6_suffix_060, kindSupport6_suffix_061, kindSupport6_suffix_062, kindSupport6_suffix_063, kindSupport6_suffix_064, kindSupport6_suffix_065, kindSupport6_suffix_066, kindSupport6_suffix_067, kindSupport6_suffix_068, kindSupport6_suffix_069, kindSupport6_suffix_070, kindSupport6_suffix_071, kindSupport6_suffix_072, kindSupport6_suffix_073, kindSupport6_suffix_074, kindSupport6_suffix_075, kindSupport6_suffix_076, kindSupport6_suffix_077, kindSupport6_suffix_078, kindSupport6_suffix_079, kindSupport6_suffix_080, kindSupport6_suffix_081, kindSupport6_suffix_082, kindSupport6_suffix_083, kindSupport6_suffix_084, kindSupport6_suffix_085, kindSupport6_suffix_086, kindSupport6_suffix_087, kindSupport6_suffix_088, kindSupport6_suffix_089, kindSupport6_suffix_090, kindSupport6_suffix_091, kindSupport6_suffix_092, kindSupport6_suffix_093, kindSupport6_suffix_094, kindSupport6_suffix_095, kindSupport6_suffix_096, kindSupport6_suffix_097, kindSupport6_suffix_098, kindSupport6_suffix_099, kindSupport6_suffix_100, kindSupport6_suffix_101, kindSupport6_suffix_102, kindSupport6_suffix_103, kindSupport6_suffix_104, kindSupport6_suffix_105, kindSupport6_suffix_106, kindSupport6_suffix_107, kindSupport6_suffix_108, kindSupport6_suffix_109, kindSupport6_suffix_110, kindSupport6_suffix_111, kindSupport6_suffix_112, kindSupport6_suffix_113, kindSupport6_suffix_114, kindSupport6_suffix_115, kindSupport6_suffix_116, kindSupport6_suffix_117, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport6_000_mask, kindSupport6_001_mask, kindSupport6_002_mask, kindSupport6_003_mask, kindSupport6_004_mask, kindSupport6_005_mask, kindSupport6_006_mask, kindSupport6_007_mask, kindSupport6_008_mask, kindSupport6_009_mask, kindSupport6_010_mask, kindSupport6_011_mask, kindSupport6_012_mask, kindSupport6_013_mask, kindSupport6_014_mask, kindSupport6_015_mask, kindSupport6_016_mask, kindSupport6_017_mask, kindSupport6_018_mask, kindSupport6_019_mask, kindSupport6_020_mask, kindSupport6_021_mask, kindSupport6_022_mask, kindSupport6_023_mask, kindSupport6_024_mask, kindSupport6_025_mask, kindSupport6_026_mask, kindSupport6_027_mask, kindSupport6_028_mask, kindSupport6_029_mask, kindSupport6_030_mask, kindSupport6_031_mask, kindSupport6_032_mask, kindSupport6_033_mask, kindSupport6_034_mask, kindSupport6_035_mask, kindSupport6_036_mask, kindSupport6_037_mask, kindSupport6_038_mask, kindSupport6_039_mask, kindSupport6_040_mask, kindSupport6_041_mask, kindSupport6_042_mask, kindSupport6_043_mask, kindSupport6_044_mask, kindSupport6_045_mask, kindSupport6_046_mask, kindSupport6_047_mask, kindSupport6_048_mask, kindSupport6_049_mask, kindSupport6_050_mask, kindSupport6_051_mask, kindSupport6_052_mask, kindSupport6_053_mask, kindSupport6_054_mask, kindSupport6_055_mask, kindSupport6_056_mask, kindSupport6_057_mask, kindSupport6_058_mask, kindSupport6_059_mask, kindSupport6_060_mask, kindSupport6_061_mask, kindSupport6_062_mask, kindSupport6_063_mask, kindSupport6_064_mask, kindSupport6_065_mask, kindSupport6_066_mask, kindSupport6_067_mask, kindSupport6_068_mask, kindSupport6_069_mask, kindSupport6_070_mask, kindSupport6_071_mask, kindSupport6_072_mask, kindSupport6_073_mask, kindSupport6_074_mask, kindSupport6_075_mask, kindSupport6_076_mask, kindSupport6_077_mask, kindSupport6_078_mask, kindSupport6_079_mask, kindSupport6_080_mask, kindSupport6_081_mask, kindSupport6_082_mask, kindSupport6_083_mask, kindSupport6_084_mask, kindSupport6_085_mask, kindSupport6_086_mask, kindSupport6_087_mask, kindSupport6_088_mask, kindSupport6_089_mask, kindSupport6_090_mask, kindSupport6_091_mask, kindSupport6_092_mask, kindSupport6_093_mask, kindSupport6_094_mask, kindSupport6_095_mask, kindSupport6_096_mask, kindSupport6_097_mask, kindSupport6_098_mask, kindSupport6_099_mask, kindSupport6_100_mask, kindSupport6_101_mask, kindSupport6_102_mask, kindSupport6_103_mask, kindSupport6_104_mask, kindSupport6_105_mask, kindSupport6_106_mask, kindSupport6_107_mask, kindSupport6_108_mask, kindSupport6_109_mask, kindSupport6_110_mask, kindSupport6_111_mask, kindSupport6_112_mask, kindSupport6_113_mask, kindSupport6_114_mask, kindSupport6_115_mask, kindSupport6_116_mask]
    decide +kernel
  · rw [kindSupport6_eq]
    simp only [kindSupport6_suffix_000, kindSupport6_suffix_001, kindSupport6_suffix_002, kindSupport6_suffix_003, kindSupport6_suffix_004, kindSupport6_suffix_005, kindSupport6_suffix_006, kindSupport6_suffix_007, kindSupport6_suffix_008, kindSupport6_suffix_009, kindSupport6_suffix_010, kindSupport6_suffix_011, kindSupport6_suffix_012, kindSupport6_suffix_013, kindSupport6_suffix_014, kindSupport6_suffix_015, kindSupport6_suffix_016, kindSupport6_suffix_017, kindSupport6_suffix_018, kindSupport6_suffix_019, kindSupport6_suffix_020, kindSupport6_suffix_021, kindSupport6_suffix_022, kindSupport6_suffix_023, kindSupport6_suffix_024, kindSupport6_suffix_025, kindSupport6_suffix_026, kindSupport6_suffix_027, kindSupport6_suffix_028, kindSupport6_suffix_029, kindSupport6_suffix_030, kindSupport6_suffix_031, kindSupport6_suffix_032, kindSupport6_suffix_033, kindSupport6_suffix_034, kindSupport6_suffix_035, kindSupport6_suffix_036, kindSupport6_suffix_037, kindSupport6_suffix_038, kindSupport6_suffix_039, kindSupport6_suffix_040, kindSupport6_suffix_041, kindSupport6_suffix_042, kindSupport6_suffix_043, kindSupport6_suffix_044, kindSupport6_suffix_045, kindSupport6_suffix_046, kindSupport6_suffix_047, kindSupport6_suffix_048, kindSupport6_suffix_049, kindSupport6_suffix_050, kindSupport6_suffix_051, kindSupport6_suffix_052, kindSupport6_suffix_053, kindSupport6_suffix_054, kindSupport6_suffix_055, kindSupport6_suffix_056, kindSupport6_suffix_057, kindSupport6_suffix_058, kindSupport6_suffix_059, kindSupport6_suffix_060, kindSupport6_suffix_061, kindSupport6_suffix_062, kindSupport6_suffix_063, kindSupport6_suffix_064, kindSupport6_suffix_065, kindSupport6_suffix_066, kindSupport6_suffix_067, kindSupport6_suffix_068, kindSupport6_suffix_069, kindSupport6_suffix_070, kindSupport6_suffix_071, kindSupport6_suffix_072, kindSupport6_suffix_073, kindSupport6_suffix_074, kindSupport6_suffix_075, kindSupport6_suffix_076, kindSupport6_suffix_077, kindSupport6_suffix_078, kindSupport6_suffix_079, kindSupport6_suffix_080, kindSupport6_suffix_081, kindSupport6_suffix_082, kindSupport6_suffix_083, kindSupport6_suffix_084, kindSupport6_suffix_085, kindSupport6_suffix_086, kindSupport6_suffix_087, kindSupport6_suffix_088, kindSupport6_suffix_089, kindSupport6_suffix_090, kindSupport6_suffix_091, kindSupport6_suffix_092, kindSupport6_suffix_093, kindSupport6_suffix_094, kindSupport6_suffix_095, kindSupport6_suffix_096, kindSupport6_suffix_097, kindSupport6_suffix_098, kindSupport6_suffix_099, kindSupport6_suffix_100, kindSupport6_suffix_101, kindSupport6_suffix_102, kindSupport6_suffix_103, kindSupport6_suffix_104, kindSupport6_suffix_105, kindSupport6_suffix_106, kindSupport6_suffix_107, kindSupport6_suffix_108, kindSupport6_suffix_109, kindSupport6_suffix_110, kindSupport6_suffix_111, kindSupport6_suffix_112, kindSupport6_suffix_113, kindSupport6_suffix_114, kindSupport6_suffix_115, kindSupport6_suffix_116, kindSupport6_suffix_117, List.all_append, List.all_nil, kindSupport6_000_checked, kindSupport6_001_checked, kindSupport6_002_checked, kindSupport6_003_checked, kindSupport6_004_checked, kindSupport6_005_checked, kindSupport6_006_checked, kindSupport6_007_checked, kindSupport6_008_checked, kindSupport6_009_checked, kindSupport6_010_checked, kindSupport6_011_checked, kindSupport6_012_checked, kindSupport6_013_checked, kindSupport6_014_checked, kindSupport6_015_checked, kindSupport6_016_checked, kindSupport6_017_checked, kindSupport6_018_checked, kindSupport6_019_checked, kindSupport6_020_checked, kindSupport6_021_checked, kindSupport6_022_checked, kindSupport6_023_checked, kindSupport6_024_checked, kindSupport6_025_checked, kindSupport6_026_checked, kindSupport6_027_checked, kindSupport6_028_checked, kindSupport6_029_checked, kindSupport6_030_checked, kindSupport6_031_checked, kindSupport6_032_checked, kindSupport6_033_checked, kindSupport6_034_checked, kindSupport6_035_checked, kindSupport6_036_checked, kindSupport6_037_checked, kindSupport6_038_checked, kindSupport6_039_checked, kindSupport6_040_checked, kindSupport6_041_checked, kindSupport6_042_checked, kindSupport6_043_checked, kindSupport6_044_checked, kindSupport6_045_checked, kindSupport6_046_checked, kindSupport6_047_checked, kindSupport6_048_checked, kindSupport6_049_checked, kindSupport6_050_checked, kindSupport6_051_checked, kindSupport6_052_checked, kindSupport6_053_checked, kindSupport6_054_checked, kindSupport6_055_checked, kindSupport6_056_checked, kindSupport6_057_checked, kindSupport6_058_checked, kindSupport6_059_checked, kindSupport6_060_checked, kindSupport6_061_checked, kindSupport6_062_checked, kindSupport6_063_checked, kindSupport6_064_checked, kindSupport6_065_checked, kindSupport6_066_checked, kindSupport6_067_checked, kindSupport6_068_checked, kindSupport6_069_checked, kindSupport6_070_checked, kindSupport6_071_checked, kindSupport6_072_checked, kindSupport6_073_checked, kindSupport6_074_checked, kindSupport6_075_checked, kindSupport6_076_checked, kindSupport6_077_checked, kindSupport6_078_checked, kindSupport6_079_checked, kindSupport6_080_checked, kindSupport6_081_checked, kindSupport6_082_checked, kindSupport6_083_checked, kindSupport6_084_checked, kindSupport6_085_checked, kindSupport6_086_checked, kindSupport6_087_checked, kindSupport6_088_checked, kindSupport6_089_checked, kindSupport6_090_checked, kindSupport6_091_checked, kindSupport6_092_checked, kindSupport6_093_checked, kindSupport6_094_checked, kindSupport6_095_checked, kindSupport6_096_checked, kindSupport6_097_checked, kindSupport6_098_checked, kindSupport6_099_checked, kindSupport6_100_checked, kindSupport6_101_checked, kindSupport6_102_checked, kindSupport6_103_checked, kindSupport6_104_checked, kindSupport6_105_checked, kindSupport6_106_checked, kindSupport6_107_checked, kindSupport6_108_checked, kindSupport6_109_checked, kindSupport6_110_checked, kindSupport6_111_checked, kindSupport6_112_checked, kindSupport6_113_checked, kindSupport6_114_checked, kindSupport6_115_checked, kindSupport6_116_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
