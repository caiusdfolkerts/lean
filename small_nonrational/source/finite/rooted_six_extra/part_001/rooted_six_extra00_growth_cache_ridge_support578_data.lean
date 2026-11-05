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
def ridgeSupport578_000 : List Nat := [11,41,51,57,62,63,154,155,158,159,162,163,226,227,230,231,234,235,295,297,299,301,303,308,309,311,314,316,318,320,322,324]
def ridgeSupport578_001 : List Nat := [329,330,332,335,649,650,651,652,653,654,717,719,721,722,724,726,727,731,736,738,740,742,743,745,747,748,752,757,805,806,807,808]
def ridgeSupport578_002 : List Nat := [809,810,873,875,877,878,880,882,883,887,892,894,896,898,899,901,903,904,908,913,957,959,961,962,964,966,967,971,976,978,980,982]
def ridgeSupport578_003 : List Nat := [983,985,987,988,992,997,1020,1021,1023,1024,1027,1028,1029,1031,1032,1034,1041,1042,1870,1875,1876,1881,1940,1941,1954,1955,1960,1962,1968,1969,1974,1975]
def ridgeSupport578_004 : List Nat := [1981,1983,1988,1989,2002,2003,2036,2037,2038,2043,2044,2049,2050,2051,2064,2065,2070,2071,2088,2089,2094,2095,2374,2379,2380,2385,2396,2397,2410,2411,2444,2445]
def ridgeSupport578_005 : List Nat := [2458,2459,2464,2466,2472,2473,2478,2479,2485,2487,2492,2493,2494,2499,2500,2505,2506,2507,2540,2541,2554,2555,2564,2565,2578,2579,2656,2661,2686,2691,2700,2701]
def ridgeSupport578_006 : List Nat := [2718,2719,2728,2733,2758,2763,2772,2773,2790,2791,3142,3147,3148,3153,3164,3165,3178,3179,3212,3213,3226,3227,3232,3234,3240,3241,3246,3247,3253,3255,3260,3261]
def ridgeSupport578_007 : List Nat := [3262,3267,3268,3273,3274,3275,3308,3309,3322,3323,3332,3333,3346,3347,3424,3429,3454,3459,3468,3469,3486,3487,3496,3501,3526,3531,3540,3541,3558,3559,4198,4203]
def ridgeSupport578_008 : List Nat := [4204,4209,4220,4221,4234,4235,4268,4269,4282,4283,4288,4290,4296,4297,4302,4303,4309,4311,4316,4317,4318,4323,4324,4329,4330,4331,4364,4365,4378,4379,4388,4389]
def ridgeSupport578_009 : List Nat := [4402,4403,4732,4737,4744,4749,4776,4777,4788,4789,4804,4809,4816,4821,4848,4849,4860,4861,5260,5265,5272,5277,5304,5305,5316,5317,5332,5337,5344,5349,5376,5377]
def ridgeSupport578_010 : List Nat := [5388,5389,7078,7079,7148,7149,7244,7245,7364,7365,7676,7677,7690,7691,7700,7701,7703,7704,7705,7707,7768,7770,7789,7791,7808,7809,7811,7812,7813,7815,7841,7842]
def ridgeSupport578_011 : List Nat := [7843,7844,7859,7860,7861,7862,7936,7938,7957,7959,7976,7977,7979,7980,7981,7983,8009,8010,8011,8012,8027,8028,8029,8030,8176,8178,8197,8199,8216,8217,8219,8220]
def ridgeSupport578_012 : List Nat := [8221,8223,8303,8304,8305,8306,8321,8322,8323,8324,8423,8424,8425,8426,8441,8442,8443,8444]
def ridgeSupport578_code : Nat := 0x83f20fb83ea0f983aa0e983a20e78212083820a08181ca07181c206f807e01d807201b8066018801e0057fc9ff07d79f5d7d71f5b7d31f4b7d29f497cbdf2d7cb1f2b7ca5f287c5df157c09f007ad9eb57ad1eb37a91ea37a89ea17a1de857a11e837a05e8079bde6d7969e58786de197861e177855e14782de0a77f5dfc7315cc47135c4c6fb5bec6e9dba6543550c540550053954e053654d453154c452e54b85275498524548c4bf52fc4bc52f04b552d04b252c44ad52b44aa52a84a352884a0527c44cd1324495124446d11a443510c43ad0ea43a50e4438d0de43750dc435d0d5433d0ce43250c843090c042ed0ba42b50ac422d08a41f507c41c506c41ad066379cde63754dd4372cdc636b4da8367cd9e3634d8c360cd7e3594d60344cd123414d0433eccfa33b4cec332ccca3324cc4330ccbe32f4cbc32dccb532bccae32a4ca83288ca0326cc9a3234c8c31acc6a3174c5c3144c4c312cc462b9cae62b54ad42b2cac62ab4aa82a7ca9e2a34a8c2a0ca7e2994a60284ca122814a0427ec9fa27b49ec272c9ca27249c4270c9be26f49bc26dc9b526bc9ae26a49a826889a0266c99a263498c25ac96a257495c254494c252c94620bc82e20a4828205c8162044810200c80220047fc1fec7f61fd47f41f4c7d21f147c41efc7bd1edc7b61ec47b01ea87a81e8c7a21e547941d647541d4c74e10484111028408101c405101040310003ff0ff43fc0f943e00f703db0f643d70f583d40f483d00f2c3c70f183c40f083c10efc3bd0e4438c0e203870e143830e083800df837c0ddc3730dc83700db836d0dac3690ca83290ca03270c983250bd42f00bb02eb0ba42e70b982e40b882e00b6c2d70b582d40b482d10b3c2cd0a3828d0a3028b0a28289053c14c05281490510142050013e04f013a04dc13504d012f04b412b04a412703ac0ea039c0e6038c0e2028c0a2027c09e026c09a00fc03e00e403300a400b
def ridgeSupport578_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport578_code
def ridgeSupport578_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport578_code
def ridgeSupport578_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport578_code
def ridgeSupport578_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport578_code
def ridgeSupport578_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport578_code
def ridgeSupport578_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport578_code
def ridgeSupport578_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport578_code
def ridgeSupport578_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport578_code
def ridgeSupport578_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport578_code
def ridgeSupport578_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport578_code
def ridgeSupport578_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport578_code
def ridgeSupport578_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport578_code
def ridgeSupport578_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport578_code
def ridgeSupport578_rest_013 : Nat := PackedRawNatGrowth.drop 5628 ridgeSupport578_code
def ridgeSupport578_suffix_013 : List Nat := []
def ridgeSupport578_suffix_012 : List Nat := ridgeSupport578_012 ++ ridgeSupport578_suffix_013
def ridgeSupport578_suffix_011 : List Nat := ridgeSupport578_011 ++ ridgeSupport578_suffix_012
def ridgeSupport578_suffix_010 : List Nat := ridgeSupport578_010 ++ ridgeSupport578_suffix_011
def ridgeSupport578_suffix_009 : List Nat := ridgeSupport578_009 ++ ridgeSupport578_suffix_010
def ridgeSupport578_suffix_008 : List Nat := ridgeSupport578_008 ++ ridgeSupport578_suffix_009
def ridgeSupport578_suffix_007 : List Nat := ridgeSupport578_007 ++ ridgeSupport578_suffix_008
def ridgeSupport578_suffix_006 : List Nat := ridgeSupport578_006 ++ ridgeSupport578_suffix_007
def ridgeSupport578_suffix_005 : List Nat := ridgeSupport578_005 ++ ridgeSupport578_suffix_006
def ridgeSupport578_suffix_004 : List Nat := ridgeSupport578_004 ++ ridgeSupport578_suffix_005
def ridgeSupport578_suffix_003 : List Nat := ridgeSupport578_003 ++ ridgeSupport578_suffix_004
def ridgeSupport578_suffix_002 : List Nat := ridgeSupport578_002 ++ ridgeSupport578_suffix_003
def ridgeSupport578_suffix_001 : List Nat := ridgeSupport578_001 ++ ridgeSupport578_suffix_002
def ridgeSupport578_suffix_000 : List Nat := ridgeSupport578_000 ++ ridgeSupport578_suffix_001
theorem ridgeSupport578_source : candidateSupports 578 =
    (PackedRawNatGrowth.readList 14 402 ridgeSupport578_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
