module
prelude
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport641_000 : List Nat := [13,23,29,32,34,180,181,182,183,184,185,252,253,254,255,256,257,295,299,300,301,302,304,305,312,314,338,340,342,343,345,347]
def ridgeSupport641_001 : List Nat := [348,352,357,408,409,410,411,412,413,451,455,456,457,458,460,461,468,470,494,496,498,499,501,503,504,508,513,535,539,540,541,542]
def ridgeSupport641_002 : List Nat := [544,545,552,554,578,580,582,583,585,587,588,592,597,598,600,602,604,605,607,609,610,614,616,621,622,1888,1893,1902,1904,1922,1923,1932]
def ridgeSupport641_003 : List Nat := [1933,1970,1971,1980,1981,1986,1987,1990,1992,1996,1997,2003,2006,2008,2013,2018,2019,2022,2024,2028,2029,2066,2067,2076,2077,2090,2091,2100,2101,2128,2133,2142]
def ridgeSupport641_004 : List Nat := [2144,2162,2163,2172,2173,2210,2211,2220,2221,2226,2227,2230,2232,2236,2237,2243,2246,2248,2253,2258,2259,2262,2264,2268,2269,2306,2307,2316,2317,2330,2331,2340]
def ridgeSupport641_005 : List Nat := [2341,2670,2672,2682,2684,2710,2711,2722,2723,2812,2817,2824,2829,2856,2857,2868,2869,2896,2901,2910,2912,2930,2931,2940,2941,2978,2979,2988,2989,2994,2995,2998]
def ridgeSupport641_006 : List Nat := [3000,3004,3005,3011,3014,3016,3021,3026,3027,3030,3032,3036,3037,3074,3075,3084,3085,3098,3099,3108,3109,3438,3440,3450,3452,3478,3479,3490,3491,3580,3585,3592]
def ridgeSupport641_007 : List Nat := [3597,3624,3625,3636,3637,3966,3968,3978,3980,4006,4007,4018,4019,4108,4113,4120,4125,4152,4153,4164,4165,7080,7081,7116,7117,7212,7213,7678,7680,7691,7694,7709]
def ridgeSupport641_008 : List Nat := [7710,7711,7712,7717,7718,7726,7728,7739,7742,7757,7758,7759,7760,7765,7766,7846,7847,7849,7851,7883,7884,7885,7886,7894,7896,7907,7910,7925,7926,7927,7928,7933]
def ridgeSupport641_009 : List Nat := [7934,8014,8015,8017,8019,8051,8052,8053,8054,8134,8135,8137,8139,8171,8172,8173,8174]
def ridgeSupport641_code : Nat := 0x1fee7fb5fec7fadfcb7f25fc77f19f767dd5f747dcdf537d45f4f7d39efe7bf5ef87bddef67bd5ee67b8ded87b59ece7b35ecc7b2deab7aa5ea77a99e567955e50793de4e7935e3e78ede3078b9e267895e20787de1e7875e0e782de0077f9c2d70b1bcd6f31ba96ea1045411103940e101d40610114030fb33ec8fa73e98f8c3e28f803df8e3538d0e2938a0e0d3820e0137f0da33688d973658d7c35e8d7035b8c253090c1b3068c0d3030c033008bdd2f70bd82f58bd32f48bcd2f20bc62f0cbbd2ef0bb82ed8bb32ec8bad2eb0ba32e88b7d2df0b732dc8b602d78b552d40b352cd0b292ca0b0d2c20b012bf0aa32a88a972a58a7c29e8a7029b8925249091b246890d243090324088dd23708d823588d323488cd23208c6230c8bd22f08b822d88b322c88ad22b08a3228887d21f087321c88602178855214083520d082b20a881d207081320487ed1fb07e81f987e31f887dd1f607d61f4c7cd1f307c81f187c31f087bd1ef07b31ec878d1e307831e087701db87651d8026e09b42680998262098425f097425c09682580958255094024c092c249091c246091024208a82280884220087821d087021b085c20107f01f807dc1f507cc1f207c01ee07581d407341cc07281c907201c7070c19d067019b06681990660165058015c056c159055c156055015204e813804c413004b812d04b012b049c10104000ff03f80fd03f00b902e00b702d80b502d0022008001d005c00d
def ridgeSupport641_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport641_code
def ridgeSupport641_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport641_code
def ridgeSupport641_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport641_code
def ridgeSupport641_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport641_code
def ridgeSupport641_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport641_code
def ridgeSupport641_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport641_code
def ridgeSupport641_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport641_code
def ridgeSupport641_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport641_code
def ridgeSupport641_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport641_code
def ridgeSupport641_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport641_code
def ridgeSupport641_rest_010 : Nat := PackedRawNatGrowth.drop 4270 ridgeSupport641_code
def ridgeSupport641_suffix_010 : List Nat := []
def ridgeSupport641_suffix_009 : List Nat := ridgeSupport641_009 ++ ridgeSupport641_suffix_010
def ridgeSupport641_suffix_008 : List Nat := ridgeSupport641_008 ++ ridgeSupport641_suffix_009
def ridgeSupport641_suffix_007 : List Nat := ridgeSupport641_007 ++ ridgeSupport641_suffix_008
def ridgeSupport641_suffix_006 : List Nat := ridgeSupport641_006 ++ ridgeSupport641_suffix_007
def ridgeSupport641_suffix_005 : List Nat := ridgeSupport641_005 ++ ridgeSupport641_suffix_006
def ridgeSupport641_suffix_004 : List Nat := ridgeSupport641_004 ++ ridgeSupport641_suffix_005
def ridgeSupport641_suffix_003 : List Nat := ridgeSupport641_003 ++ ridgeSupport641_suffix_004
def ridgeSupport641_suffix_002 : List Nat := ridgeSupport641_002 ++ ridgeSupport641_suffix_003
def ridgeSupport641_suffix_001 : List Nat := ridgeSupport641_001 ++ ridgeSupport641_suffix_002
def ridgeSupport641_suffix_000 : List Nat := ridgeSupport641_000 ++ ridgeSupport641_suffix_001
theorem ridgeSupport641_source : candidateSupports 641 =
    (PackedRawNatGrowth.readList 14 305 ridgeSupport641_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
