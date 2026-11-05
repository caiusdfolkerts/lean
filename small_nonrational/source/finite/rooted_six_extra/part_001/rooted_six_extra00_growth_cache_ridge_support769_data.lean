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
def ridgeSupport769_000 : List Nat := [14,24,30,33,34,192,193,194,195,196,197,264,265,266,267,268,269,316,320,321,322,323,325,326,333,335,337,341,342,343,344,346]
def ridgeSupport769_001 : List Nat := [347,354,356,420,421,422,423,424,425,472,476,477,478,479,481,482,489,491,493,497,498,499,500,502,503,510,512,556,560,561,562,563]
def ridgeSupport769_002 : List Nat := [565,566,573,575,577,581,582,583,584,586,587,594,596,598,599,603,604,605,606,608,609,617,619,620,622,1890,1892,1896,1898,1928,1929,1934]
def ridgeSupport769_003 : List Nat := [1935,1976,1977,1982,1983,1984,1985,1990,1991,1996,1998,2002,2004,2010,2012,2016,2018,2024,2025,2030,2031,2072,2073,2078,2079,2096,2097,2102,2103,2130,2132,2136]
def ridgeSupport769_004 : List Nat := [2138,2168,2169,2174,2175,2216,2217,2222,2223,2224,2225,2230,2231,2236,2238,2242,2244,2250,2252,2256,2258,2264,2265,2270,2271,2312,2313,2318,2319,2336,2337,2342]
def ridgeSupport769_005 : List Nat := [2343,2742,2744,2754,2756,2782,2783,2794,2795,2814,2816,2826,2828,2854,2855,2866,2867,2898,2900,2904,2906,2936,2937,2942,2943,2984,2985,2990,2991,2992,2993,2998]
def ridgeSupport769_006 : List Nat := [2999,3004,3006,3010,3012,3018,3020,3024,3026,3032,3033,3038,3039,3080,3081,3086,3087,3104,3105,3110,3111,3510,3512,3522,3524,3550,3551,3562,3563,3582,3584,3594]
def ridgeSupport769_007 : List Nat := [3596,3622,3623,3634,3635,4038,4040,4050,4052,4078,4079,4090,4091,4110,4112,4122,4124,4150,4151,4162,4163,7082,7083,7118,7119,7214,7215,7684,7686,7690,7692,7708]
def ridgeSupport769_008 : List Nat := [7709,7711,7713,7714,7715,7732,7734,7738,7740,7756,7757,7759,7761,7762,7763,7864,7865,7867,7869,7882,7883,7885,7887,7900,7902,7906,7908,7924,7925,7927,7929,7930]
def ridgeSupport769_009 : List Nat := [7931,8032,8033,8035,8037,8050,8051,8053,8055,8152,8153,8155,8157,8170,8171,8173,8175]
def ridgeSupport769_code : Nat := 0x1fef7fb5feb7fa9fdd7f6dfd97f61f777dd5f737dc9f657d8df617d81efb7be9ef97bddef57bd1ee47b89ede7b71ecf7b35ecb7b29ebd7aedeb97ae1e537949e51793de4d7931e3c78e9e3678d1e237889e21787de1d7871e0c7829e067811c2f70b9bcf6f39bab6ea9043410903740d901c40690104038ffb3fe8fef3fb8fd43f48fc83f18e3338c8e273898e0c3828e0037f8deb37a8ddf3778dc43708db836d8c273098c213080c0f3038c093020bdf2f78bd92f60bd22f40bcc2f28bc42f08bbe2ef0bb72ed8bb12ec0baf2eb8ba92ea0b7f2df8b792de0b5a2d60b542d48b332cc8b272c98b0c2c28b002bf8aeb2ba8adf2b78ac42b08ab82ad89272498921248090f243890924208df23788d923608d223408cc23288c423088be22f08b722d88b122c08af22b88a922a087f21f887921e085a2160854214883720d883120c081f207881920607ef1fb87e91fa07e21f807dc1f687d41f487ce1f307c71f187c11f007bf1ef87b91ee078f1e387891e2076a1da07641d8826e09b026b09a4261098025e097425c096c2570958254094824b0928248091c246091424108fc23d08d823508cc23208c423008b020007f81f707d81f407cc1f207c41ed07ac1e907881e1077c1de07741dc07601a906a01a706981a50690164058815b0568158055c1560554151053c14d0518145050c142050414004f010d043010b042810904200c503100c303080c10300022008401e006000e
def ridgeSupport769_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport769_code
def ridgeSupport769_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport769_code
def ridgeSupport769_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport769_code
def ridgeSupport769_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport769_code
def ridgeSupport769_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport769_code
def ridgeSupport769_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport769_code
def ridgeSupport769_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport769_code
def ridgeSupport769_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport769_code
def ridgeSupport769_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport769_code
def ridgeSupport769_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport769_code
def ridgeSupport769_rest_010 : Nat := PackedRawNatGrowth.drop 4270 ridgeSupport769_code
def ridgeSupport769_suffix_010 : List Nat := []
def ridgeSupport769_suffix_009 : List Nat := ridgeSupport769_009 ++ ridgeSupport769_suffix_010
def ridgeSupport769_suffix_008 : List Nat := ridgeSupport769_008 ++ ridgeSupport769_suffix_009
def ridgeSupport769_suffix_007 : List Nat := ridgeSupport769_007 ++ ridgeSupport769_suffix_008
def ridgeSupport769_suffix_006 : List Nat := ridgeSupport769_006 ++ ridgeSupport769_suffix_007
def ridgeSupport769_suffix_005 : List Nat := ridgeSupport769_005 ++ ridgeSupport769_suffix_006
def ridgeSupport769_suffix_004 : List Nat := ridgeSupport769_004 ++ ridgeSupport769_suffix_005
def ridgeSupport769_suffix_003 : List Nat := ridgeSupport769_003 ++ ridgeSupport769_suffix_004
def ridgeSupport769_suffix_002 : List Nat := ridgeSupport769_002 ++ ridgeSupport769_suffix_003
def ridgeSupport769_suffix_001 : List Nat := ridgeSupport769_001 ++ ridgeSupport769_suffix_002
def ridgeSupport769_suffix_000 : List Nat := ridgeSupport769_000 ++ ridgeSupport769_suffix_001
theorem ridgeSupport769_source : candidateSupports 769 =
    (PackedRawNatGrowth.readList 14 305 ridgeSupport769_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
