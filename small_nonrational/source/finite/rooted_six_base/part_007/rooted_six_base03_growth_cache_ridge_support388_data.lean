module
prelude
public import RootedSixBase03GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport388_000 : List Nat := [18,38,68,74,77,80,152,153,154,155,162,163,349,350,351,354,355,360,361,366,368,411,412,416,418,419,423,425,426,428,577,578]
def ridgeSupport388_001 : List Nat := [581,582,585,586,614,615,616,619,620,625,626,631,633,676,677,681,683,684,688,690,691,693,1000,1001,1002,1003,1004,1005,1034,1038,1039,1040]
def ridgeSupport388_002 : List Nat := [1041,1043,1044,1051,1053,1099,1100,1101,1104,1105,1106,1108,1113,1115,1118,1122,1123,1124,1125,1127,1128,1135,1137,1183,1184,1185,1188,1189,1190,1192,1197,1199]
def ridgeSupport388_003 : List Nat := [1202,1205,1206,1207,1210,1211,1212,1214,1219,1220,1222,1223,1759,1761,1766,1768,1786,1787,1789,1792,1795,1798,1800,1801,1814,1815,1820,1821,1834,1835,1848,1849]
def ridgeSupport388_004 : List Nat := [1855,1857,1862,1863,1868,1869,1874,1876,1879,1880,1887,1888,1891,1893,1898,1900,1918,1919,1921,1924,1927,1930,1932,1933,1946,1947,1952,1953,1966,1967,1980,1981]
def ridgeSupport388_005 : List Nat := [1987,1989,1994,1995,2000,2001,2006,2008,2011,2012,2019,2020,2022,2023,2030,2032,2034,2035,2042,2044,2058,2059,2070,2071,2188,2189,2191,2193,2200,2201,2203,2205]
def ridgeSupport388_006 : List Nat := [2224,2225,2236,2237,2731,2733,2738,2740,2750,2751,2756,2757,2770,2771,2773,2776,2779,2782,2784,2785,2791,2793,2798,2799,2804,2805,2810,2812,2818,2819,2832,2833]
def ridgeSupport388_007 : List Nat := [2841,2843,2844,2846,2994,2995,3151,3153,3158,3160,3170,3171,3176,3177,3190,3191,3193,3196,3199,3202,3204,3205,3211,3213,3218,3219,3224,3225,3230,3232,3238,3239]
def ridgeSupport388_008 : List Nat := [3252,3253,3261,3263,3264,3266,3272,3274,3276,3277,3294,3295,3302,3304,3312,3313,3321,3323,3433,3435,3442,3443,3460,3461,3463,3465,3478,3479,3480,3482,3980,3982]
def ridgeSupport388_009 : List Nat := [3984,3985,3992,3994,3996,3997,4005,4007,4011,4013,4141,4143,4150,4151,4153,4155,4162,4163,4164,4166,4170,4172,4411,4413,4418,4420,4423,4425,4430,4432,4434,4435]
def ridgeSupport388_010 : List Nat := [4456,4457,4506,4508,4515,4517,4542,4544,4551,4553,4556,4558,4573,4575,4629,4631,4644,4646,4738,4739,4774,4775,4932,4933,5064,5065]
def ridgeSupport388_code : Nat := 0x27933c89a2cd1254f2a6941ca0a44d22490bc8563bf1dd8e747323931c78e046fa34b1a38ce466a2d31688a9c54a2a114e8a4c51e28914289ec4ee09904a823411208704281dc0e606f036817c0b5f5afab7d3be95f3af9c7cd3e61f22f907c73e31b34d986cbb659b12d876c2b611ae6d726b5b5a59f6cf9678b3c19d0ce666fb37999accc6653321984cc065fb2f596acb4653b299940c9e64cb261926c92646b22d90ac8464131fd8f8c7963bb1d98d2c68631b1898b0c56628b13d766bb258f2c71636b19588ac41606b0257e2be95eaaf4577abb95d2ae7570ab815bcadb56c2b555a6ad2562ab1157eabe55a2ac955aaab45ea2f11628b044ea26d132898448a23d11a88c40ba05901680a3fe1fe8fe67f23f81fb8fce7e63f21f8cfb87db3ec1f58fa27d03e59f28f8a7c33de9ef0f5e7ae3d09e80f3679a3c69e30f147873c21e04efe77e3b61da8eca7633b01d7ceb07573aa1d48e9a74c3a39d18e8273f39c9ce0e5672a38e9c70e2e7163849c20e0c7033801bf4df66fa3741b98dc26df26393189884c325f12f09764ba25b92d896a4b225792b49504a625292909424a024f91c48de46823391948c846323111788b645922a11488a2450226913089641d20d9050826411208103c81c40a1f68fb07d63ea1f48fa056a2b31590ac05582ab1548a9454827913b89c84e226c13589a04ce266125092448c24512109043581aa0d4869c3461a20d006703361700b705a42d01630b1057c2bc15d051828813609a04c82600a004d025011004c012
def ridgeSupport388_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport388_code
def ridgeSupport388_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport388_code
def ridgeSupport388_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport388_code
def ridgeSupport388_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport388_code
def ridgeSupport388_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport388_code
def ridgeSupport388_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport388_code
def ridgeSupport388_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport388_code
def ridgeSupport388_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport388_code
def ridgeSupport388_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport388_code
def ridgeSupport388_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport388_code
def ridgeSupport388_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport388_code
def ridgeSupport388_rest_011 : Nat := PackedRawNatGrowth.drop 4498 ridgeSupport388_code
def ridgeSupport388_suffix_011 : List Nat := []
def ridgeSupport388_suffix_010 : List Nat := ridgeSupport388_010 ++ ridgeSupport388_suffix_011
def ridgeSupport388_suffix_009 : List Nat := ridgeSupport388_009 ++ ridgeSupport388_suffix_010
def ridgeSupport388_suffix_008 : List Nat := ridgeSupport388_008 ++ ridgeSupport388_suffix_009
def ridgeSupport388_suffix_007 : List Nat := ridgeSupport388_007 ++ ridgeSupport388_suffix_008
def ridgeSupport388_suffix_006 : List Nat := ridgeSupport388_006 ++ ridgeSupport388_suffix_007
def ridgeSupport388_suffix_005 : List Nat := ridgeSupport388_005 ++ ridgeSupport388_suffix_006
def ridgeSupport388_suffix_004 : List Nat := ridgeSupport388_004 ++ ridgeSupport388_suffix_005
def ridgeSupport388_suffix_003 : List Nat := ridgeSupport388_003 ++ ridgeSupport388_suffix_004
def ridgeSupport388_suffix_002 : List Nat := ridgeSupport388_002 ++ ridgeSupport388_suffix_003
def ridgeSupport388_suffix_001 : List Nat := ridgeSupport388_001 ++ ridgeSupport388_suffix_002
def ridgeSupport388_suffix_000 : List Nat := ridgeSupport388_000 ++ ridgeSupport388_suffix_001
theorem ridgeSupport388_source : candidateSupports 388 =
    (PackedRawNatGrowth.readList 13 346 ridgeSupport388_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
