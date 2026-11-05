module
prelude
public import RootedSixBase01GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport449_000 : List Nat := [272,273,274,428,429,430,512,513,514,606,607,608,1668,1669,1670,1671,1672,1673,1716,1717,1718,1719,1720,1721,1860,1861,1862,1863,1864,1865,1932,1933]
def ridgeSupport449_001 : List Nat := [1934,1935,1936,1937,1980,1981,1982,1983,1984,1985,2124,2125,2126,2127,2128,2129,2430,2431,2432,2433,2434,2435,2442,2443,2444,2445,2446,2447,2892,2893,2894,2895]
def ridgeSupport449_002 : List Nat := [2896,2897,2940,2941,2942,2943,2944,2945,3084,3085,3086,3087,3088,3089,3390,3391,3392,3393,3394,3395,3402,3403,3404,3405,3406,3407,4086,4087,4088,4089,4090,4091]
def ridgeSupport449_003 : List Nat := [4098,4099,4100,4101,4102,4103,7170,7172,7176,7178,7182,7184,7198,7199,7204,7205,7210,7211,7246,7247,7252,7253,7258,7259,7338,7340,7344,7346,7350,7352,7380,7381]
def ridgeSupport449_004 : List Nat := [7382,7383,7384,7385,7410,7412,7416,7418,7422,7424,7438,7439,7444,7445,7450,7451,7486,7487,7492,7493,7498,7499,7578,7580,7584,7586,7590,7592,7620,7621,7622,7623]
def ridgeSupport449_005 : List Nat := [7624,7625,7938,7939,7940,7941,7942,7943,7950,7951,7952,7953,7954,7955,8178,8180,8184,8186,8190,8192,8206,8207,8212,8213,8218,8219,8254,8255,8260,8261,8266,8267]
def ridgeSupport449_006 : List Nat := [8346,8348,8352,8354,8358,8360,8388,8389,8390,8391,8392,8393,8706,8707,8708,8709,8710,8711,8718,8719,8720,8721,8722,8723,9234,9235,9236,9237,9238,9239,9246,9247]
def ridgeSupport449_007 : List Nat := [9248,9249,9250,9251,11634,11636,11640,11730,11732,11736,11738,11742,11744,11766,11768,11772,11862,11864,11868,11870,11874,11876,12078,12079,12080,12081,12082,12083,12246,12248,12252,12342]
def ridgeSupport449_008 : List Nat := [12344,12348,12350,12354,12356,12558,12559,12560,12561,12562,12563,12906,12907,12908,12909,12910,12911,14683,14685,14689,14691,14695,14697,14719,14721,14725,14727,14731,14733,14815,14817,14821]
def ridgeSupport449_009 : List Nat := [14823,14827,14829]
def ridgeSupport449_code : Nat := 0x39ede7af9e7e7979e1e77f98de62f987e617981e5ff969e59f963e58795de56f26fc9bb26dc9b326bc9ab113c44b111c44310fc43b044c10b03ec0f3038c0dafdcbf62fd6bccef32bcc6f30bcbef2eb992e62b97ae5cb962e56b7f2df8b7dade0b77addab762dd4b74ad78b5d2d72908e4229086420907e41e905e4169056414904e412884e2128846210883e20e881e2068816204880e20283260c8831e0c683160c482a20a6828a0a0827209a812e04a811604480fe03e806e01a8056014803e00e8001ffe7fe9ff87fd1ff27c4df127c45f107c3df0e7c1df067c15f047c0df027725dc8771ddc67715dc476a1da67689da07671d9a752dd4a7515d4474fdd3e746dd1a7455d14743dd0e7401cfe73e9cf873d1cf27365cd8735dcd67355cd472e1cb672c9cb072b1caa716dc5a7155c54713dc4e70adc2a7095c24707dc1e7041c0e7029c087011c02401d0064015004400d0023fecffa3fe4ff83fdcff6353cd4e3534d4c352cd4a350cd423504d4034fcd3e3044c10303cc0e3034c0c2e04b802dfcb7e2df4b7c2d44b502d3cb4e2d34b4c263c98e263498c262c98a260c982260498025fc97e2144850213c84e213484c1f047c01efc7be1ef47bc1e447901e3c78e1e3478c1d247481d1c7461d147441ae46b81adc6b61ad46b41a246881a1c6861a14684098025f0978202080420006b81ad06b01120444110
def ridgeSupport449_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport449_code
def ridgeSupport449_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport449_code
def ridgeSupport449_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport449_code
def ridgeSupport449_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport449_code
def ridgeSupport449_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport449_code
def ridgeSupport449_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport449_code
def ridgeSupport449_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport449_code
def ridgeSupport449_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport449_code
def ridgeSupport449_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport449_code
def ridgeSupport449_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport449_code
def ridgeSupport449_rest_010 : Nat := PackedRawNatGrowth.drop 4074 ridgeSupport449_code
def ridgeSupport449_suffix_010 : List Nat := []
def ridgeSupport449_suffix_009 : List Nat := ridgeSupport449_009 ++ ridgeSupport449_suffix_010
def ridgeSupport449_suffix_008 : List Nat := ridgeSupport449_008 ++ ridgeSupport449_suffix_009
def ridgeSupport449_suffix_007 : List Nat := ridgeSupport449_007 ++ ridgeSupport449_suffix_008
def ridgeSupport449_suffix_006 : List Nat := ridgeSupport449_006 ++ ridgeSupport449_suffix_007
def ridgeSupport449_suffix_005 : List Nat := ridgeSupport449_005 ++ ridgeSupport449_suffix_006
def ridgeSupport449_suffix_004 : List Nat := ridgeSupport449_004 ++ ridgeSupport449_suffix_005
def ridgeSupport449_suffix_003 : List Nat := ridgeSupport449_003 ++ ridgeSupport449_suffix_004
def ridgeSupport449_suffix_002 : List Nat := ridgeSupport449_002 ++ ridgeSupport449_suffix_003
def ridgeSupport449_suffix_001 : List Nat := ridgeSupport449_001 ++ ridgeSupport449_suffix_002
def ridgeSupport449_suffix_000 : List Nat := ridgeSupport449_000 ++ ridgeSupport449_suffix_001
theorem ridgeSupport449_source : candidateRows 449 =
    (PackedRawNatGrowth.readList 14 291 ridgeSupport449_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase01
