module
prelude
public import RootedSixBase02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport644_000 : List Nat := [19,35,61,64,66,150,151,152,153,160,161,356,357,358,361,362,367,368,373,375,397,399,401,403,405,410,411,413,416,553,554,555]
def ridgeSupport644_001 : List Nat := [558,559,564,565,570,572,594,596,598,600,602,607,608,610,613,901,905,906,907,908,910,911,918,920,944,946,948,949,951,953,954,958]
def ridgeSupport644_002 : List Nat := [963,964,966,968,970,971,973,975,976,980,982,987,988,1628,1633,1642,1644,1710,1711,1720,1721,1726,1727,1730,1732,1736,1737,1743,1746,1758,1759,1768]
def ridgeSupport644_003 : List Nat := [1769,1796,1801,1806,1807,1810,1812,1816,1817,1822,1823,1832,1833,1846,1847,1856,1857,1868,1873,1882,1884,1950,1951,1960,1961,1966,1967,1970,1972,1976,1977,1983]
def ridgeSupport644_004 : List Nat := [1986,1998,1999,2008,2009,2036,2041,2046,2047,2050,2052,2056,2057,2062,2063,2072,2073,2086,2087,2096,2097,2188,2190,2200,2202,2216,2217,2228,2229,2330,2335,2342]
def ridgeSupport644_005 : List Nat := [2347,2362,2363,2374,2375,3188,3193,3202,3204,3222,3223,3232,3233,3270,3271,3280,3281,3286,3287,3290,3292,3296,3297,3303,3306,3308,3313,3318,3319,3322,3324,3328]
def ridgeSupport644_006 : List Nat := [3329,3366,3367,3376,3377,3390,3391,3400,3401,3710,3711,3722,3723,4814,4815,4822,4823,5264,5269,5270,5274,5290,5291,5294,5296,5300,5301,5307,5310,5322,5323,5332]
def ridgeSupport644_007 : List Nat := [5333,5338,5339,5348,5349,5360,5365,5370,5371,5374,5376,5380,5381,5384,5386,5390,5391,5396,5401,5402,5406,5422,5423,5426,5428,5432,5433,5439,5442,5454,5455,5464]
def ridgeSupport644_008 : List Nat := [5465,5470,5471,5480,5481,5492,5497,5502,5503,5506,5508,5512,5513,5516,5518,5522,5523,5582,5583,5590,5592,5594,5595,5602,5604,5618,5619,5630,5631,5692,5693,5696]
def ridgeSupport644_009 : List Nat := [5701,5704,5705,5708,5713,5728,5729,5740,5741,6236,6241,6242,6246,6258,6259,6268,6269,6274,6275,6278,6280,6284,6285,6291,6294,6296,6301,6306,6307,6310,6312,6316]
def ridgeSupport644_010 : List Nat := [6317,6322,6323,6332,6333,6348,6349,6353,6355,6504,6505,7140,7141,7376,7381,7382,7386,7388,7393,7394,7398,7406,7407,7420,7421,7473,7476,7479,7483,7642,7643,7678]
def ridgeSupport644_011 : List Nat := [7679,7840,7841]
def ridgeSupport644_code : Nat := 0x7a87d41dffeff776fbb5d3be9bf4d3a63cfde7e73bf9ddce6e7173879b9cdae6b73579a1be5df265a72d18d3c68e3371998bdc5e62cf1658adc5662a314d8a3c516277131896c49e237119888c43620f10587dc3e61cf0e5866c3161870b966db365986cc1651b265926c91645b2058f6c795ffaff57cebe55e4af1576ebb55d8aeb573eb9d593ac9563ab19589ac45612b0557fabf55e6ae9569ab4557eabd559aac553ea9d542a9fd4e6a71534a9954bea5d51ea8d5466a2950fa87542aa11505a8254029fd4fba7d53d69e14e5a72536e9b54d5a6a532e9954bea5dd2d69694b0a5752ae95549aa4b52569212d796b4b3e59ce8b74539fdcfcd496a434fda7cd31698349da4cd0168033f19f4cf767b33c59d8cea673b3859c0cdc66d335d9accd1668331d98cca1650325d92cc8464131e58e89474a324ed27492b493247d2348b545a22a515089a44c2239118831418209d04c81940c203d01c80940420110047ff3ff1fe4fe87d93ec1f3cf9c7c23df9ee4f707b43d91ebcf5c7a93d41e7cf3c75c3ad1d44e987413a01cdce6c7293941c7ce3c71938c1c50e2470f3871c24e086e93741b7cdbc6d23679b24d906c43611afcd7c6b935c1abcd5c66c3351984cb83dc1ed8f587a83d01e78f347963ca1e40f187883c31df0ee87723b71da8ed07643b01cc0e5871e38e1c60e2c7143891c289944c426012f89684b025612a094847823a11a88d045e22e11588a84521a00ce866c3341950c9864431e18d0bb85d42e016f0b505a42cc1650b2028414009904c025c12c04202000f4046013
def ridgeSupport644_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport644_code
def ridgeSupport644_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport644_code
def ridgeSupport644_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport644_code
def ridgeSupport644_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport644_code
def ridgeSupport644_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport644_code
def ridgeSupport644_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport644_code
def ridgeSupport644_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport644_code
def ridgeSupport644_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport644_code
def ridgeSupport644_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport644_code
def ridgeSupport644_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport644_code
def ridgeSupport644_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport644_code
def ridgeSupport644_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport644_code
def ridgeSupport644_rest_012 : Nat := PackedRawNatGrowth.drop 4615 ridgeSupport644_code
def ridgeSupport644_suffix_012 : List Nat := []
def ridgeSupport644_suffix_011 : List Nat := ridgeSupport644_011 ++ ridgeSupport644_suffix_012
def ridgeSupport644_suffix_010 : List Nat := ridgeSupport644_010 ++ ridgeSupport644_suffix_011
def ridgeSupport644_suffix_009 : List Nat := ridgeSupport644_009 ++ ridgeSupport644_suffix_010
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
    (PackedRawNatGrowth.readList 13 355 ridgeSupport644_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
