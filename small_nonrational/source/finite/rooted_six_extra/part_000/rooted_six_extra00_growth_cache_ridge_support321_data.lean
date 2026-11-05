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
def ridgeSupport321_000 : List Nat := [10,20,26,31,33,144,145,146,147,148,149,216,217,218,219,220,221,275,277,279,280,282,284,285,289,294,318,319,320,323,324,325]
def ridgeSupport321_001 : List Nat := [327,332,334,372,373,374,375,376,377,431,433,435,436,438,440,441,445,450,474,475,476,479,480,481,483,488,490,515,517,519,520,522]
def ridgeSupport321_002 : List Nat := [524,525,529,534,558,559,560,563,564,565,567,572,574,599,601,602,604,605,607,609,610,612,613,617,618,1895,1897,1906,1911,1914,1915,1924]
def ridgeSupport321_003 : List Nat := [1925,1962,1963,1972,1973,1985,1988,1994,1995,1999,2001,2004,2005,2010,2011,2015,2017,2020,2021,2026,2031,2058,2059,2068,2069,2082,2083,2092,2093,2135,2137,2146]
def ridgeSupport321_004 : List Nat := [2151,2154,2155,2164,2165,2202,2203,2212,2213,2225,2228,2234,2235,2239,2241,2244,2245,2250,2251,2255,2257,2260,2261,2266,2271,2298,2299,2308,2309,2322,2323,2332]
def ridgeSupport321_005 : List Nat := [2333,2596,2601,2608,2613,2640,2641,2652,2653,2741,2743,2753,2755,2786,2787,2798,2799,2903,2905,2914,2919,2922,2923,2932,2933,2970,2971,2980,2981,2993,2996,3002]
def ridgeSupport321_006 : List Nat := [3003,3007,3009,3012,3013,3018,3019,3023,3025,3028,3029,3034,3039,3066,3067,3076,3077,3090,3091,3100,3101,3364,3369,3376,3381,3408,3409,3420,3421,3509,3511,3521]
def ridgeSupport321_007 : List Nat := [3523,3554,3555,3566,3567,3892,3897,3904,3909,3936,3937,3948,3949,4037,4039,4049,4051,4082,4083,4094,4095,7074,7075,7110,7111,7206,7207,7673,7676,7687,7689,7710]
def ridgeSupport321_008 : List Nat := [7711,7714,7716,7717,7718,7721,7724,7735,7737,7758,7759,7762,7764,7765,7766,7829,7830,7831,7832,7864,7866,7868,7869,7889,7892,7903,7905,7926,7927,7930,7932,7933]
def ridgeSupport321_009 : List Nat := [7934,7997,7998,7999,8000,8032,8034,8036,8037,8117,8118,8119,8120,8152,8154,8156,8157]
def ridgeSupport321_code : Nat := 0x1fdd7f71fda7f61fb87eddfb67ed5f657d91f627d81f407cfdf3e7cf5efe7bf5efc7be9ef77bd9ee17b7ded47b45ebd7af1eba7ae1e987a5de967a55e567955e547949e4f7939e3978dde2c78a5e267895e247889e1f7879e09781ddfc77e5c277099bc76f19ba36e88fff3ff8ff33fc8fd33f44fc73f14f6d3db0f613d80f453d00f393cd0def37b8de33788dc33704db736d4d5d3570d513540d3534c0d293490c1d3070c133048c053010bfb2fe8bdf2f68bd52f50bd12f3cbcb2f28bc52f10bc12efcbbb2ee8bb42ec4ba52e90b9b2e68b752dd0b6b2da8b672d88b592d5caef2bb8ae32b88ac32b04ab72ad4a5d2970a512940a3528c0a29289091d2470913244890524108fb23e88df23688d523508d1233c8cb23288c523108c122fc8bb22e88b422c48a5229089b226887521d086b21a88672188859215c82d20b08232088815205080b20287ef1fa87e51f907e11f7c7db1f687d51f507d11f3c7cb1f287c41f047b51ed07ab1ea87851e1077b1de87771dc87691d9c26a09a42650990262098425f097425c0968259095c23e08f023708d423408cc23008bc22e0858211083420c0828208081c205080c1ea07a01e307841e0077c1dc076c1da07081bd06e41b806d81b406cc1b106bc17905e017705d817505d014e05301470514144050c14004fc13e0498121047411c0468118045c115044c0dd03700db03680d90360095025009302480910240021007c01a005000a
def ridgeSupport321_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport321_code
def ridgeSupport321_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport321_code
def ridgeSupport321_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport321_code
def ridgeSupport321_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport321_code
def ridgeSupport321_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport321_code
def ridgeSupport321_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport321_code
def ridgeSupport321_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport321_code
def ridgeSupport321_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport321_code
def ridgeSupport321_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport321_code
def ridgeSupport321_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport321_code
def ridgeSupport321_rest_010 : Nat := PackedRawNatGrowth.drop 4270 ridgeSupport321_code
def ridgeSupport321_suffix_010 : List Nat := []
def ridgeSupport321_suffix_009 : List Nat := ridgeSupport321_009 ++ ridgeSupport321_suffix_010
def ridgeSupport321_suffix_008 : List Nat := ridgeSupport321_008 ++ ridgeSupport321_suffix_009
def ridgeSupport321_suffix_007 : List Nat := ridgeSupport321_007 ++ ridgeSupport321_suffix_008
def ridgeSupport321_suffix_006 : List Nat := ridgeSupport321_006 ++ ridgeSupport321_suffix_007
def ridgeSupport321_suffix_005 : List Nat := ridgeSupport321_005 ++ ridgeSupport321_suffix_006
def ridgeSupport321_suffix_004 : List Nat := ridgeSupport321_004 ++ ridgeSupport321_suffix_005
def ridgeSupport321_suffix_003 : List Nat := ridgeSupport321_003 ++ ridgeSupport321_suffix_004
def ridgeSupport321_suffix_002 : List Nat := ridgeSupport321_002 ++ ridgeSupport321_suffix_003
def ridgeSupport321_suffix_001 : List Nat := ridgeSupport321_001 ++ ridgeSupport321_suffix_002
def ridgeSupport321_suffix_000 : List Nat := ridgeSupport321_000 ++ ridgeSupport321_suffix_001
theorem ridgeSupport321_source : candidateSupports 321 =
    (PackedRawNatGrowth.readList 14 305 ridgeSupport321_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
