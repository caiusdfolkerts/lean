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
def ridgeSupport386_000 : List Nat := [12,38,48,54,57,60,152,153,156,157,160,161,224,225,228,229,232,233,261,262,263,266,267,272,273,278,280,323,324,328,330,331]
def ridgeSupport386_001 : List Nat := [335,337,338,340,579,580,581,582,583,584,613,617,618,619,620,622,623,630,632,678,679,680,683,684,685,687,692,694,735,736,737,738]
def ridgeSupport386_002 : List Nat := [739,740,769,773,774,775,776,778,779,786,788,834,835,836,839,840,841,843,848,850,853,857,858,859,860,862,863,870,872,918,919,920]
def ridgeSupport386_003 : List Nat := [923,924,925,927,932,934,937,940,941,942,945,946,947,949,954,955,957,958,1627,1629,1634,1636,1654,1655,1657,1660,1663,1666,1668,1669,1682,1683]
def ridgeSupport386_004 : List Nat := [1688,1689,1702,1703,1716,1717,1723,1725,1730,1731,1736,1737,1742,1744,1747,1748,1755,1756,1903,1905,1910,1912,1922,1923,1928,1929,1942,1943,1945,1948,1951,1954]
def ridgeSupport386_005 : List Nat := [1956,1957,1963,1965,1970,1971,1976,1977,1982,1984,1990,1991,2004,2005,2013,2015,2016,2018,2024,2026,2028,2029,2046,2047,2054,2056,2064,2065,2073,2075,2185,2187]
def ridgeSupport386_006 : List Nat := [2194,2195,2212,2213,2215,2217,2230,2231,2232,2234,2383,2385,2390,2392,2402,2403,2408,2409,2422,2423,2425,2428,2431,2434,2436,2437,2443,2445,2450,2451,2456,2457]
def ridgeSupport386_007 : List Nat := [2462,2464,2470,2471,2484,2485,2493,2495,2496,2498,2504,2506,2508,2509,2526,2527,2534,2536,2544,2545,2553,2555,2665,2667,2674,2675,2692,2693,2695,2697,2710,2711]
def ridgeSupport386_008 : List Nat := [2712,2714,3019,3021,3026,3028,3038,3039,3044,3045,3058,3059,3061,3064,3067,3070,3072,3073,3079,3081,3086,3087,3092,3093,3098,3100,3106,3107,3120,3121,3129,3131]
def ridgeSupport386_009 : List Nat := [3132,3134,3284,3286,3288,3289,3296,3298,3300,3301,3309,3311,3315,3317,3445,3447,3454,3455,3457,3459,3466,3467,3468,3470,3474,3476,3632,3634,3636,3637,3644,3646]
def ridgeSupport386_010 : List Nat := [3648,3649,3657,3659,3663,3665,3793,3795,3802,3803,3805,3807,3814,3815,3816,3818,3822,3824,4399,4401,4406,4408,4422,4424,4431,4433,4436,4438,4453,4455,4470,4472]
def ridgeSupport386_011 : List Nat := [4479,4481,4484,4486,4501,4503,4530,4532,4539,4541,4557,4559,4572,4574,4593,4595,4608,4610,4702,4703,4776,4777,4872,4873,5028,5029]
def ridgeSupport386_code : Nat := 0x274b3a4984cc225532a892fc97a4052008f9c7c63bd1dc8e7c73637b1bb8da46ca32f1958c3461230317f8bc45da2cf1658ab45522a314f8a4451a271136898c4bdde0eee7753ba1dceee676fbb75db6eda769bb45ca2e4f725b925c82e4071f38f1c6ae3471938c1b28d926c73631b16d8a6c1b605afed7e6bbb5d59eacf3677b3b59cace467133819b2cd866b335187cc3c61db0e5862c30611b089838c1a60ab05181ec0e604b01d802c005ff2fed7f0bf55f9afc97cabe45efaf797a8bd25e6af2d534a9854baa59512a87542aa114e6a72535a9a53f69f94f8a7c13d09e64efa77939a9cc4e527213849c04dfa6f536a9b44d3a69934099e4cca6613269924c6a62d30a9844c125fd2f89794bba5d92d29684b1a5892b09564a8a53d1748b845ba2d91528a7452a291126892445a225036819408a0410108063ff9ff8fda7ec3f51fa0fc47e03ef9f74faa7d43e39f18f807be3dc9ee0f667b23d69eacf4a7a43d11e7cf387993cb9e58f127883c19e08ef07763b89dbcdb86db36a1b4cda06ce3649b20d866c235e9aecd6a6b43539a98d326983499a48d0a68434119fccf867933b99d8cc866232e996c77c3bd1dd8ee876a3b31d90ec475c3ad1d60ea474c3a41cf8e7473839b1cc0e5c72c3681b30d7c6bc35c1ad8d686b23551a90d406963491a40d1c6883431a10c5062430b1850c2060e3061828c045c82e31710b845c02df15b0ad055e2ad1560aac5502a715309e04ec26f13709b04d626a134899449024712309144882430aa05482a214f0a585282901440a1846022c111088042c21410708304141d20e807283901c20e0050828013a09c04c826007803901b00c004c00c
def ridgeSupport386_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport386_code
def ridgeSupport386_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport386_code
def ridgeSupport386_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport386_code
def ridgeSupport386_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport386_code
def ridgeSupport386_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport386_code
def ridgeSupport386_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport386_code
def ridgeSupport386_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport386_code
def ridgeSupport386_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport386_code
def ridgeSupport386_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport386_code
def ridgeSupport386_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport386_code
def ridgeSupport386_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport386_code
def ridgeSupport386_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport386_code
def ridgeSupport386_rest_012 : Nat := PackedRawNatGrowth.drop 4914 ridgeSupport386_code
def ridgeSupport386_suffix_012 : List Nat := []
def ridgeSupport386_suffix_011 : List Nat := ridgeSupport386_011 ++ ridgeSupport386_suffix_012
def ridgeSupport386_suffix_010 : List Nat := ridgeSupport386_010 ++ ridgeSupport386_suffix_011
def ridgeSupport386_suffix_009 : List Nat := ridgeSupport386_009 ++ ridgeSupport386_suffix_010
def ridgeSupport386_suffix_008 : List Nat := ridgeSupport386_008 ++ ridgeSupport386_suffix_009
def ridgeSupport386_suffix_007 : List Nat := ridgeSupport386_007 ++ ridgeSupport386_suffix_008
def ridgeSupport386_suffix_006 : List Nat := ridgeSupport386_006 ++ ridgeSupport386_suffix_007
def ridgeSupport386_suffix_005 : List Nat := ridgeSupport386_005 ++ ridgeSupport386_suffix_006
def ridgeSupport386_suffix_004 : List Nat := ridgeSupport386_004 ++ ridgeSupport386_suffix_005
def ridgeSupport386_suffix_003 : List Nat := ridgeSupport386_003 ++ ridgeSupport386_suffix_004
def ridgeSupport386_suffix_002 : List Nat := ridgeSupport386_002 ++ ridgeSupport386_suffix_003
def ridgeSupport386_suffix_001 : List Nat := ridgeSupport386_001 ++ ridgeSupport386_suffix_002
def ridgeSupport386_suffix_000 : List Nat := ridgeSupport386_000 ++ ridgeSupport386_suffix_001
theorem ridgeSupport386_source : candidateSupports 386 =
    (PackedRawNatGrowth.readList 13 378 ridgeSupport386_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
