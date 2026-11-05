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
def ridgeSupport580_000 : List Nat := [17,33,59,64,65,126,127,128,129,136,137,355,357,359,361,363,368,369,371,374,376,378,380,382,384,389,390,392,395,552,554,556]
def ridgeSupport580_001 : List Nat := [558,560,565,566,568,571,573,575,577,579,581,586,587,589,592,902,904,906,907,909,911,912,916,921,923,925,927,928,930,932,933,937]
def ridgeSupport580_002 : List Nat := [942,965,966,968,969,972,973,974,976,977,979,986,987,1634,1639,1640,1645,1704,1705,1718,1719,1724,1726,1732,1733,1738,1739,1745,1747,1752,1753,1766]
def ridgeSupport580_003 : List Nat := [1767,1800,1801,1802,1807,1808,1813,1814,1815,1828,1829,1834,1835,1852,1853,1858,1859,1874,1879,1880,1885,1944,1945,1958,1959,1964,1966,1972,1973,1978,1979,1985]
def ridgeSupport580_004 : List Nat := [1987,1992,1993,2006,2007,2040,2041,2042,2047,2048,2053,2054,2055,2068,2069,2074,2075,2092,2093,2098,2099,2186,2191,2198,2203,2218,2219,2230,2231,2258,2263,2270]
def ridgeSupport580_005 : List Nat := [2275,2290,2291,2302,2303,3194,3199,3200,3205,3216,3217,3230,3231,3264,3265,3278,3279,3284,3286,3292,3293,3298,3299,3305,3307,3312,3313,3314,3319,3320,3325,3326]
def ridgeSupport580_006 : List Nat := [3327,3360,3361,3374,3375,3384,3385,3398,3399,3678,3679,3690,3691,4782,4783,4790,4791,5144,5146,5153,5155,5156,5158,5165,5167,5176,5177,5182,5183,5241,5243,5248]
def ridgeSupport580_007 : List Nat := [5250,5414,5415,5450,5451,5604,5605,5904,5905,5918,5919,5928,5929,5931,5932,5933,5935,5952,5953,5966,5967,5976,5977,5979,5980,5981,5983,6015,6016,6017,6018,6033]
def ridgeSupport580_008 : List Nat := [6034,6035,6036,6236,6238,6257,6259,6276,6277,6279,6280,6281,6283]
def ridgeSupport580_code : Nat := 0x188bc44e22310f885c4261cf0e385ec2e5e52f27792bc8de0af03780bbfdd7eebb75cbaddd66eb174fba75d06e8172fb96dcb2e57729b945c7ee3d711b885796bc954baa5549ea4d482a4051ee8f343fa1f50e687142fa16d09a849423a10d06a8312b795b4abe55ce6b735397dcbcd476a334e5a70d2f6973485a40cff67f33f59f0cf767933c59e0ceb674b38d9c4cdd66e33599a8ccf6673305980c9f64f3245920c8564031fd8f48ff47f23cd1e48e346f235d1a48b745b22ad15489b44b223d11483341920b505881b40d205502880740320150007ff3fd1fe4ff07d73eb1f24f907c33e09eecf747b53da1eb8f587a73d31e64f3075d3ac1d5cea47433a11cf4e7872b3951c94e4871738b1c54e2070f3851c24e106e73731b64db06d33689b2cd946c53621af8d786b735b1aa4d5066d334199ccc43db1ed0f4c7a23d01e70f347983c91e40f1878a3ae1d48e947483a21d00e7c73a39b1cc8e5072038f1c68e2c7143881c3094049a24b125091448624111f88f447623811b08d446022e11608a845018b0c4061830a1800bf05f02f41780bb05cc2e21700b585a42ce1650b1822411008104001fc0fc04102000ec042011
def ridgeSupport580_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport580_code
def ridgeSupport580_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport580_code
def ridgeSupport580_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport580_code
def ridgeSupport580_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport580_code
def ridgeSupport580_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport580_code
def ridgeSupport580_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport580_code
def ridgeSupport580_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport580_code
def ridgeSupport580_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport580_code
def ridgeSupport580_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport580_code
def ridgeSupport580_rest_009 : Nat := PackedRawNatGrowth.drop 3497 ridgeSupport580_code
def ridgeSupport580_suffix_009 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 269 ridgeSupport580_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
