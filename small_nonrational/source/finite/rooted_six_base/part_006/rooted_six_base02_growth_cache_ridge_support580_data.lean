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
def ridgeSupport580_000 : List Nat := [17,33,59,64,65,126,127,128,129,136,137,355,357,359,361,363,368,369,371,374,376,378,380,382,384,389,390,392,395,552,554,556]
def ridgeSupport580_001 : List Nat := [558,560,565,566,568,571,573,575,577,579,581,586,587,589,592,902,904,906,907,909,911,912,916,921,923,925,927,928,930,932,933,937]
def ridgeSupport580_002 : List Nat := [942,965,966,968,969,972,973,974,976,977,979,986,987,1634,1639,1640,1645,1704,1705,1718,1719,1724,1726,1732,1733,1738,1739,1745,1747,1752,1753,1766]
def ridgeSupport580_003 : List Nat := [1767,1800,1801,1802,1807,1808,1813,1814,1815,1828,1829,1834,1835,1852,1853,1858,1859,1874,1879,1880,1885,1944,1945,1958,1959,1964,1966,1972,1973,1978,1979,1985]
def ridgeSupport580_004 : List Nat := [1987,1992,1993,2006,2007,2040,2041,2042,2047,2048,2053,2054,2055,2068,2069,2074,2075,2092,2093,2098,2099,2186,2191,2198,2203,2218,2219,2230,2231,2258,2263,2270]
def ridgeSupport580_005 : List Nat := [2275,2290,2291,2302,2303,3194,3199,3200,3205,3216,3217,3230,3231,3264,3265,3278,3279,3284,3286,3292,3293,3298,3299,3305,3307,3312,3313,3314,3319,3320,3325,3326]
def ridgeSupport580_006 : List Nat := [3327,3360,3361,3374,3375,3384,3385,3398,3399,3678,3679,3690,3691,4782,4783,4790,4791,5264,5266,5273,5275,5288,5290,5296,5297,5302,5303,5309,5311,5316,5317,5330]
def ridgeSupport580_007 : List Nat := [5331,5344,5345,5350,5351,5364,5365,5366,5371,5372,5377,5378,5379,5387,5389,5390,5392,5396,5398,5405,5407,5420,5422,5428,5429,5434,5435,5441,5443,5448,5449,5462]
def ridgeSupport580_008 : List Nat := [5463,5476,5477,5482,5483,5496,5497,5498,5503,5504,5509,5510,5511,5519,5521,5522,5524,5584,5585,5588,5593,5596,5597,5600,5605,5620,5621,5632,5633,5638,5639,5642]
def ridgeSupport580_009 : List Nat := [5647,5650,5651,5654,5659,5674,5675,5686,5687,6236,6238,6245,6247,6252,6253,6266,6267,6272,6274,6280,6281,6286,6287,6293,6295,6300,6301,6302,6307,6308,6313,6314]
def ridgeSupport580_010 : List Nat := [6315,6328,6329,6334,6335,6345,6346,6353,6354,6496,6497,7132,7133,7376,7378,7385,7387,7388,7390,7397,7399,7408,7409,7414,7415,7473,7475,7480,7482,7646,7647,7682]
def ridgeSupport580_011 : List Nat := [7683,7836,7837]
def ridgeSupport580_code : Nat := 0x7a77d39e03f01777fbbdd3ae9c74cfa63cf7e7b73c79e1ce7e72f37b9b9cdbe6cf34b9a1bdddee65872c18d2c68e32b1938bfc5f62e71718abc5562a71498a3c4f6277139897c4ae23f11d889c44620b10187bc3d61b70d9867c32e17b0b9637b1b58aec5561bb0b584ec2560fb05581ec0d601b0057d6be95e5af05776bb95d9aea5746ba1594ac95646b1f587ac35616b0157fabd55e6af156bab55596ac9557aab5526a91543aa0d4eea75535a9a54baa5951fa8ed45aa29510a875436a17503a8154069f94fba7b53d69e94e7a7353869c14d3a6953169894bfa5ed2de96d4b1a5852aa95149ba4cd24a9212b795b4abe55ce6b735397dcbcd476a334e5a70d2f6973485a40cff67f33f59f0cf767933c59e0ceb674b38d9c4cdd66e33599a8ccf6673305980c9f64f3245920c8564031fd8f48ff47f23cd1e48e346f235d1a48b745b22ad15489b44b223d11483341920b505881b40d205502880740320150007ff3fd1fe4ff07d73eb1f24f907c33e09eecf747b53da1eb8f587a73d31e64f3075d3ac1d5cea47433a11cf4e7872b3951c94e4871738b1c54e2070f3851c24e106e73731b64db06d33689b2cd946c53621af8d786b735b1aa4d5066d334199ccc43db1ed0f4c7a23d01e70f347983c91e40f1878a3ae1d48e947483a21d00e7c73a39b1cc8e5072038f1c68e2c7143881c3094049a24b125091448624111f88f447623811b08d446022e11608a845018b0c4061830a1800bf05f02f41780bb05cc2e21700b585a42ce1650b1822411008104001fc0fc04102000ec042011
def ridgeSupport580_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport580_code
def ridgeSupport580_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport580_code
def ridgeSupport580_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport580_code
def ridgeSupport580_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport580_code
def ridgeSupport580_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport580_code
def ridgeSupport580_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport580_code
def ridgeSupport580_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport580_code
def ridgeSupport580_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport580_code
def ridgeSupport580_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport580_code
def ridgeSupport580_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport580_code
def ridgeSupport580_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport580_code
def ridgeSupport580_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport580_code
def ridgeSupport580_rest_012 : Nat := PackedRawNatGrowth.drop 4615 ridgeSupport580_code
def ridgeSupport580_suffix_012 : List Nat := []
def ridgeSupport580_suffix_011 : List Nat := ridgeSupport580_011 ++ ridgeSupport580_suffix_012
def ridgeSupport580_suffix_010 : List Nat := ridgeSupport580_010 ++ ridgeSupport580_suffix_011
def ridgeSupport580_suffix_009 : List Nat := ridgeSupport580_009 ++ ridgeSupport580_suffix_010
def ridgeSupport580_suffix_008 : List Nat := ridgeSupport580_008 ++ ridgeSupport580_suffix_009
def ridgeSupport580_suffix_007 : List Nat := ridgeSupport580_007 ++ ridgeSupport580_suffix_008
def ridgeSupport580_suffix_006 : List Nat := ridgeSupport580_006 ++ ridgeSupport580_suffix_007
def ridgeSupport580_suffix_005 : List Nat := ridgeSupport580_005 ++ ridgeSupport580_suffix_006
def ridgeSupport580_suffix_004 : List Nat := ridgeSupport580_004 ++ ridgeSupport580_suffix_005
def ridgeSupport580_suffix_003 : List Nat := ridgeSupport580_003 ++ ridgeSupport580_suffix_004
def ridgeSupport580_suffix_002 : List Nat := ridgeSupport580_002 ++ ridgeSupport580_suffix_003
def ridgeSupport580_suffix_001 : List Nat := ridgeSupport580_001 ++ ridgeSupport580_suffix_002
def ridgeSupport580_suffix_000 : List Nat := ridgeSupport580_000 ++ ridgeSupport580_suffix_001
theorem ridgeSupport580_source : candidateSupports 580 =
    (PackedRawNatGrowth.readList 13 355 ridgeSupport580_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
