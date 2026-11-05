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
def ridgeSupport577_000 : List Nat := [11,21,27,32,33,156,157,158,159,160,161,228,229,230,231,232,233,296,298,300,301,303,305,306,310,315,317,319,321,322,324,326]
def ridgeSupport577_001 : List Nat := [327,331,336,384,385,386,387,388,389,452,454,456,457,459,461,462,466,471,473,475,477,478,480,482,483,487,492,536,538,540,541,543]
def ridgeSupport577_002 : List Nat := [545,546,550,555,557,559,561,562,564,566,567,571,576,599,600,602,603,606,607,608,610,611,613,620,621,1894,1899,1900,1905,1916,1917,1930]
def ridgeSupport577_003 : List Nat := [1931,1964,1965,1978,1979,1984,1986,1992,1993,1998,1999,2005,2007,2012,2013,2014,2019,2020,2025,2026,2027,2060,2061,2074,2075,2084,2085,2098,2099,2134,2139,2140]
def ridgeSupport577_004 : List Nat := [2145,2156,2157,2170,2171,2204,2205,2218,2219,2224,2226,2232,2233,2238,2239,2245,2247,2252,2253,2254,2259,2260,2265,2266,2267,2300,2301,2314,2315,2324,2325,2338]
def ridgeSupport577_005 : List Nat := [2339,2668,2673,2680,2685,2712,2713,2724,2725,2740,2745,2752,2757,2784,2785,2796,2797,2902,2907,2908,2913,2924,2925,2938,2939,2972,2973,2986,2987,2992,2994,3000]
def ridgeSupport577_006 : List Nat := [3001,3006,3007,3013,3015,3020,3021,3022,3027,3028,3033,3034,3035,3068,3069,3082,3083,3092,3093,3106,3107,3436,3441,3448,3453,3480,3481,3492,3493,3508,3513,3520]
def ridgeSupport577_007 : List Nat := [3525,3552,3553,3564,3565,3964,3969,3976,3981,4008,4009,4020,4021,4036,4041,4048,4053,4080,4081,4092,4093,7076,7077,7112,7113,7208,7209,7672,7674,7693,7695,7712]
def ridgeSupport577_008 : List Nat := [7713,7715,7716,7717,7719,7720,7722,7741,7743,7760,7761,7763,7764,7765,7767,7847,7848,7849,7850,7865,7866,7867,7868,7888,7890,7909,7911,7928,7929,7931,7932,7933]
def ridgeSupport577_009 : List Nat := [7935,8015,8016,8017,8018,8033,8034,8035,8036,8135,8136,8137,8138,8153,8154,8155,8156]
def ridgeSupport577_code : Nat := 0x1fdc7f6dfda7f65fca7f25fc87f1df647d8df627d85f527d45f507d3deff7bf5efc7bedef97be1ee77b95ed27b41ebc7aedeba7ae5eaa7aa5ea87a9de577955e54794de517941e3f78f5e2a78a1e277895e24788de217881e0f7835dfa77e1c2970a1bc96f21ba56e90ffd3ff0ff13fc0fd53f40fc93f10fb53ed0fa93ea0f8d3e20f813df0ded37b0de13780dc53700db936d0da53690d993660d7d35e0d7135b0c233088c153050c0b3028bfd2ff0bdb2f68bd92f50bd32f38bcd2f30bc72f14bbf2ef8bb92ee0bb22ec0bab2ea8b9d2e70b7b2de8b6d2db0b612d70b5b2d58aed2bb0ae12b80ac52b00ab92ad0aa52a90a992a60a7d29e0a7129b09232488915245090b24288fd23f08db23688d923508d323388cd23308c723148bf22f88b922e08b222c08ab22a889d227087b21e886d21b0861217085b215883320c8825209081b206880d20307eb1fa87e91f907e31f787dd1f707d71f547cf1f387c91f207c21f007bb1ee87ad1eb078b1e2877d1df07711db076b1d9826d09b0265098c262098025f097825b0968258095c24008ec23708d823408c823108bc22d08ac2260888221087c21d087021a08601ec079c1e307881e007781dd076c1d9075c1d207381cd072c1c907201c60710185061018306081810600150052c1470518144050814104fc13d04ec13604c813104bc12d04b012a04a00e903a00e703980e503900a1028009f027809d0270021008001b005400b
def ridgeSupport577_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport577_code
def ridgeSupport577_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport577_code
def ridgeSupport577_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport577_code
def ridgeSupport577_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport577_code
def ridgeSupport577_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport577_code
def ridgeSupport577_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport577_code
def ridgeSupport577_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport577_code
def ridgeSupport577_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport577_code
def ridgeSupport577_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport577_code
def ridgeSupport577_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport577_code
def ridgeSupport577_rest_010 : Nat := PackedRawNatGrowth.drop 4270 ridgeSupport577_code
def ridgeSupport577_suffix_010 : List Nat := []
def ridgeSupport577_suffix_009 : List Nat := ridgeSupport577_009 ++ ridgeSupport577_suffix_010
def ridgeSupport577_suffix_008 : List Nat := ridgeSupport577_008 ++ ridgeSupport577_suffix_009
def ridgeSupport577_suffix_007 : List Nat := ridgeSupport577_007 ++ ridgeSupport577_suffix_008
def ridgeSupport577_suffix_006 : List Nat := ridgeSupport577_006 ++ ridgeSupport577_suffix_007
def ridgeSupport577_suffix_005 : List Nat := ridgeSupport577_005 ++ ridgeSupport577_suffix_006
def ridgeSupport577_suffix_004 : List Nat := ridgeSupport577_004 ++ ridgeSupport577_suffix_005
def ridgeSupport577_suffix_003 : List Nat := ridgeSupport577_003 ++ ridgeSupport577_suffix_004
def ridgeSupport577_suffix_002 : List Nat := ridgeSupport577_002 ++ ridgeSupport577_suffix_003
def ridgeSupport577_suffix_001 : List Nat := ridgeSupport577_001 ++ ridgeSupport577_suffix_002
def ridgeSupport577_suffix_000 : List Nat := ridgeSupport577_000 ++ ridgeSupport577_suffix_001
theorem ridgeSupport577_source : candidateSupports 577 =
    (PackedRawNatGrowth.readList 14 305 ridgeSupport577_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
