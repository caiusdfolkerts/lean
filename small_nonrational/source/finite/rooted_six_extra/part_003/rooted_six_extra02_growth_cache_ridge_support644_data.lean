module
prelude
public import RootedSixExtra02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport644_000 : List Nat := [19,35,61,64,66,150,151,152,153,160,161,356,357,358,361,362,367,368,373,375,397,399,401,403,405,410,411,413,416,553,554,555]
def ridgeSupport644_001 : List Nat := [558,559,564,565,570,572,594,596,598,600,602,607,608,610,613,901,905,906,907,908,910,911,918,920,944,946,948,949,951,953,954,958]
def ridgeSupport644_002 : List Nat := [963,964,966,968,970,971,973,975,976,980,982,987,988,1628,1633,1642,1644,1710,1711,1720,1721,1726,1727,1730,1732,1736,1737,1743,1746,1758,1759,1768]
def ridgeSupport644_003 : List Nat := [1769,1796,1801,1806,1807,1810,1812,1816,1817,1822,1823,1832,1833,1846,1847,1856,1857,1868,1873,1882,1884,1950,1951,1960,1961,1966,1967,1970,1972,1976,1977,1983]
def ridgeSupport644_004 : List Nat := [1986,1998,1999,2008,2009,2036,2041,2046,2047,2050,2052,2056,2057,2062,2063,2072,2073,2086,2087,2096,2097,2188,2190,2200,2202,2216,2217,2228,2229,2330,2335,2342]
def ridgeSupport644_005 : List Nat := [2347,2362,2363,2374,2375,3188,3193,3202,3204,3222,3223,3232,3233,3270,3271,3280,3281,3286,3287,3290,3292,3296,3297,3303,3306,3308,3313,3318,3319,3322,3324,3328]
def ridgeSupport644_006 : List Nat := [3329,3366,3367,3376,3377,3390,3391,3400,3401,3710,3711,3722,3723,4814,4815,4822,4823,5144,5149,5150,5154,5156,5161,5162,5166,5174,5175,5188,5189,5241,5244,5247]
def ridgeSupport644_007 : List Nat := [5251,5410,5411,5446,5447,5608,5609,5910,5911,5920,5921,5925,5926,5927,5928,5933,5934,5958,5959,5968,5969,5973,5974,5975,5976,5981,5982,6014,6015,6017,6019,6051]
def ridgeSupport644_008 : List Nat := [6052,6053,6054,6242,6244,6255,6258,6273,6274,6275,6276,6281,6282]
def ridgeSupport644_code : Nat := 0x188ac44e213107882c40e1cb0df864c315e9af4b7a4bd1de0ef0377fbbf5d7aebb758babdd5aeab751ba85d1ee8d72eb96dca2e4f726b92dc86e41717b8b57a6bd1547aa3548ea45483a3fd1f28f3445a2250de86d42ea1550a6849422a0f50768312d796b4b3e59ce8b74539fdcfcd496a434fda7cd31698349da4cd0168033f19f4cf767b33c59d8cea673b3859c0cdc66d335d9accd1668331d98cca1650325d92cc8464131e58e89474a324ed27492b493247d2348b545a22a515089a44c2239118831418209d04c81940c203d01c80940420110047ff3ff1fe4fe87d93ec1f3cf9c7c23df9ee4f707b43d91ebcf5c7a93d41e7cf3c75c3ad1d44e987413a01cdce6c7293941c7ce3c71938c1c50e2470f3871c24e086e93741b7cdbc6d23679b24d906c43611afcd7c6b935c1abcd5c66c3351984cb83dc1ed8f587a83d01e78f347963ca1e40f187883c31df0ee87723b71da8ed07643b01cc0e5871e38e1c60e2c7143891c289944c426012f89684b025612a094847823a11a88d045e22e11588a84521a00ce866c3341950c9864431e18d0bb85d42e016f0b505a42cc1650b2028414009904c025c12c04202000f4046013
def ridgeSupport644_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport644_code
def ridgeSupport644_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport644_code
def ridgeSupport644_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport644_code
def ridgeSupport644_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport644_code
def ridgeSupport644_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport644_code
def ridgeSupport644_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport644_code
def ridgeSupport644_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport644_code
def ridgeSupport644_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport644_code
def ridgeSupport644_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport644_code
def ridgeSupport644_rest_009 : Nat := PackedRawNatGrowth.drop 3497 ridgeSupport644_code
def ridgeSupport644_suffix_009 : List Nat := []
def ridgeSupport644_suffix_008 : List Nat := ridgeSupport644_008 ++ ridgeSupport644_suffix_009
def ridgeSupport644_suffix_007 : List Nat := ridgeSupport644_007 ++ ridgeSupport644_suffix_008
def ridgeSupport644_suffix_006 : List Nat := ridgeSupport644_006 ++ ridgeSupport644_suffix_007
def ridgeSupport644_suffix_005 : List Nat := ridgeSupport644_005 ++ ridgeSupport644_suffix_006
def ridgeSupport644_suffix_004 : List Nat := ridgeSupport644_004 ++ ridgeSupport644_suffix_005
def ridgeSupport644_suffix_003 : List Nat := ridgeSupport644_003 ++ ridgeSupport644_suffix_004
def ridgeSupport644_suffix_002 : List Nat := ridgeSupport644_002 ++ ridgeSupport644_suffix_003
def ridgeSupport644_suffix_001 : List Nat := ridgeSupport644_001 ++ ridgeSupport644_suffix_002
def ridgeSupport644_suffix_000 : List Nat := ridgeSupport644_000 ++ ridgeSupport644_suffix_001
theorem ridgeSupport644_source : candidateSupports 644 =
    (PackedRawNatGrowth.readList 13 269 ridgeSupport644_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
