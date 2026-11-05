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
def ridgeSupport196_000 : List Nat := [15,31,57,63,64,102,103,104,105,112,113,334,335,339,341,342,346,348,349,351,355,356,360,362,363,367,369,370,372,531,532,536]
def ridgeSupport196_001 : List Nat := [538,539,543,545,546,548,552,553,557,559,560,564,566,567,569,882,883,884,887,888,889,891,896,898,903,904,905,908,909,910,912,917]
def ridgeSupport196_002 : List Nat := [919,966,967,969,970,971,972,974,975,977,978,980,981,1641,1643,1647,1649,1700,1701,1706,1707,1727,1729,1733,1735,1740,1741,1746,1747,1748,1749,1754]
def ridgeSupport196_003 : List Nat := [1755,1796,1797,1802,1803,1809,1811,1815,1817,1836,1837,1842,1843,1860,1861,1866,1867,1881,1883,1887,1889,1940,1941,1946,1947,1967,1969,1973,1975,1980,1981,1986]
def ridgeSupport196_004 : List Nat := [1987,1988,1989,1994,1995,2036,2037,2042,2043,2049,2051,2055,2057,2076,2077,2082,2083,2100,2101,2106,2107,2115,2117,2127,2129,2148,2149,2160,2161,2187,2189,2199]
def ridgeSupport196_005 : List Nat := [2201,2220,2221,2232,2233,3201,3203,3207,3209,3212,3213,3218,3219,3260,3261,3266,3267,3287,3289,3293,3295,3300,3301,3306,3307,3308,3309,3314,3315,3321,3323,3327]
def ridgeSupport196_006 : List Nat := [3329,3356,3357,3362,3363,3380,3381,3386,3387,3646,3647,3658,3659,4750,4751,4758,4759,5267,5269,5271,5273,5291,5293,5297,5299,5304,5305,5310,5311,5312,5313,5318]
def ridgeSupport196_007 : List Nat := [5319,5352,5353,5358,5359,5360,5361,5366,5367,5373,5375,5379,5381,5391,5392,5394,5395,5399,5401,5403,5405,5423,5425,5429,5431,5436,5437,5442,5443,5444,5445,5450]
def ridgeSupport196_008 : List Nat := [5451,5484,5485,5490,5491,5492,5493,5498,5499,5505,5507,5511,5513,5523,5524,5526,5527,5532,5533,5535,5537,5544,5545,5547,5549,5568,5569,5580,5581,5586,5587,5589]
def ridgeSupport196_009 : List Nat := [5591,5598,5599,5601,5603,5622,5623,5634,5635,6239,6241,6243,6245,6248,6249,6254,6255,6275,6277,6281,6283,6288,6289,6294,6295,6296,6297,6302,6303,6309,6311,6315]
def ridgeSupport196_010 : List Nat := [6317,6336,6337,6342,6343,6344,6345,6347,6348,6488,6489,7124,7125,7379,7381,7383,7385,7391,7393,7395,7397,7404,7405,7410,7411,7474,7476,7478,7480,7650,7651,7686]
def ridgeSupport196_011 : List Nat := [7687,7832,7833]
def ridgeSupport196_code : Nat := 0x7a67d31e07f03778fbc5d38e9b74d3a65cf3e7973b79d9ce5e71f3879bfcd9e6bf3579a7bd5dea65672b18ccc65e3271918c7c6363071818adc55e29f14b89fc4f6267131897c4b624712188bc44e21710786fc3761a70d1865c31e1870bf603b0157debed5e3af0d77ebbd5d7aead74eba55cdae65706b815adad5d6a6b515a1acfd676b39597acb5652b27589ac3d60eb0357babd55d6ae9573ab955b6ad954baa55516a89543aa154f6a79537a9ad4c6a5f51da8dd466a2f513a895442a1f505a81d3fe9fb4f7a7b53c69e14efa7753a69d14c7a6353069814bfa5f52e69714b3a58d2b6957499a4bd25692729794b4a3e51ce4b72538fdc7cd3b69d34d5a68d236913475a38d0167fb3ed9f2cf367933b59d8ceb67533959c8cdf66eb3659aecc366132f5978c936493235918c89643b20d9028b945c22b515889944ba23511687143821950c8851427a11508683b41d20d50688234112075038809403a00d0027fb3fd1fd4fe87cb3e51f14f887c33e11ef4f787b73da9ec4f5e79b3cd1e54f287613af9d6ceb274b3a51d14e887333991cb4e5871938b9c4ce2270b3851c14e086db36d1b54da86d33691b34d986c73629b04d7e6ab3551a94d4867133799accd23d51ea0f487a23cf1e70f307963ca1e48f1c78c3971ca8e4071c38d1c60e247103871c10e006f63791bc0ddc6e83731b908e446e23611a08c045e22d11488a0448222110887c43621a10c08504261740b905c42de16b0b505a02c81630af85742b815a0ab05542a614f0a701c40e0069034019c0cc04001f80e403e00f
def ridgeSupport196_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport196_code
def ridgeSupport196_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport196_code
def ridgeSupport196_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport196_code
def ridgeSupport196_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport196_code
def ridgeSupport196_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport196_code
def ridgeSupport196_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport196_code
def ridgeSupport196_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport196_code
def ridgeSupport196_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport196_code
def ridgeSupport196_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport196_code
def ridgeSupport196_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport196_code
def ridgeSupport196_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport196_code
def ridgeSupport196_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport196_code
def ridgeSupport196_rest_012 : Nat := PackedRawNatGrowth.drop 4615 ridgeSupport196_code
def ridgeSupport196_suffix_012 : List Nat := []
def ridgeSupport196_suffix_011 : List Nat := ridgeSupport196_011 ++ ridgeSupport196_suffix_012
def ridgeSupport196_suffix_010 : List Nat := ridgeSupport196_010 ++ ridgeSupport196_suffix_011
def ridgeSupport196_suffix_009 : List Nat := ridgeSupport196_009 ++ ridgeSupport196_suffix_010
def ridgeSupport196_suffix_008 : List Nat := ridgeSupport196_008 ++ ridgeSupport196_suffix_009
def ridgeSupport196_suffix_007 : List Nat := ridgeSupport196_007 ++ ridgeSupport196_suffix_008
def ridgeSupport196_suffix_006 : List Nat := ridgeSupport196_006 ++ ridgeSupport196_suffix_007
def ridgeSupport196_suffix_005 : List Nat := ridgeSupport196_005 ++ ridgeSupport196_suffix_006
def ridgeSupport196_suffix_004 : List Nat := ridgeSupport196_004 ++ ridgeSupport196_suffix_005
def ridgeSupport196_suffix_003 : List Nat := ridgeSupport196_003 ++ ridgeSupport196_suffix_004
def ridgeSupport196_suffix_002 : List Nat := ridgeSupport196_002 ++ ridgeSupport196_suffix_003
def ridgeSupport196_suffix_001 : List Nat := ridgeSupport196_001 ++ ridgeSupport196_suffix_002
def ridgeSupport196_suffix_000 : List Nat := ridgeSupport196_000 ++ ridgeSupport196_suffix_001
theorem ridgeSupport196_source : candidateSupports 196 =
    (PackedRawNatGrowth.readList 13 355 ridgeSupport196_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
