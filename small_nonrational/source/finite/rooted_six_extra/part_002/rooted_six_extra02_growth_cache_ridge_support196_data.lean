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
def ridgeSupport196_000 : List Nat := [15,31,57,63,64,102,103,104,105,112,113,334,335,339,341,342,346,348,349,351,355,356,360,362,363,367,369,370,372,531,532,536]
def ridgeSupport196_001 : List Nat := [538,539,543,545,546,548,552,553,557,559,560,564,566,567,569,882,883,884,887,888,889,891,896,898,903,904,905,908,909,910,912,917]
def ridgeSupport196_002 : List Nat := [919,966,967,969,970,971,972,974,975,977,978,980,981,1641,1643,1647,1649,1700,1701,1706,1707,1727,1729,1733,1735,1740,1741,1746,1747,1748,1749,1754]
def ridgeSupport196_003 : List Nat := [1755,1796,1797,1802,1803,1809,1811,1815,1817,1836,1837,1842,1843,1860,1861,1866,1867,1881,1883,1887,1889,1940,1941,1946,1947,1967,1969,1973,1975,1980,1981,1986]
def ridgeSupport196_004 : List Nat := [1987,1988,1989,1994,1995,2036,2037,2042,2043,2049,2051,2055,2057,2076,2077,2082,2083,2100,2101,2106,2107,2115,2117,2127,2129,2148,2149,2160,2161,2187,2189,2199]
def ridgeSupport196_005 : List Nat := [2201,2220,2221,2232,2233,3201,3203,3207,3209,3212,3213,3218,3219,3260,3261,3266,3267,3287,3289,3293,3295,3300,3301,3306,3307,3308,3309,3314,3315,3321,3323,3327]
def ridgeSupport196_006 : List Nat := [3329,3356,3357,3362,3363,3380,3381,3386,3387,3646,3647,3658,3659,4750,4751,4758,4759,5147,5149,5151,5153,5159,5161,5163,5165,5172,5173,5178,5179,5242,5244,5246]
def ridgeSupport196_007 : List Nat := [5248,5418,5419,5454,5455,5600,5601,5900,5901,5906,5907,5924,5925,5930,5931,5934,5935,5948,5949,5954,5955,5972,5973,5978,5979,5982,5983,5996,5998,6000,6001,6014]
def ridgeSupport196_008 : List Nat := [6016,6018,6019,6239,6241,6245,6247,6272,6273,6278,6279,6282,6283]
def ridgeSupport196_code : Nat := 0x188bc45621f10d881c40619f0cb861c2fde0ef05780bbf5dc6ee176ebb65d7eebd75bbad5d56ea9743ba15cf6e7972fb975caee55725b925c4ee2570db865786bc154faa754aea55480a3f51f28f543ba1d50d686942da15d0a684f421a0fd07683729794b4a3e51ce4b72538fdc7cd3b69d34d5a68d236913475a38d0167fb3ed9f2cf367933b59d8ceb67533959c8cdf66eb3659aecc366132f5978c936493235918c89643b20d9028b945c22b515889944ba23511687143821950c8851427a11508683b41d20d50688234112075038809403a00d0027fb3fd1fd4fe87cb3e51f14f887c33e11ef4f787b73da9ec4f5e79b3cd1e54f287613af9d6ceb274b3a51d14e887333991cb4e5871938b9c4ce2270b3851c14e086db36d1b54da86d33691b34d986c73629b04d7e6ab3551a94d4867133799accd23d51ea0f487a23cf1e70f307963ca1e48f1c78c3971ca8e4071c38d1c60e247103871c10e006f63791bc0ddc6e83731b908e446e23611a08c045e22d11488a0448222110887c43621a10c08504261740b905c42de16b0b505a02c81630af85742b815a0ab05542a614f0a701c40e0069034019c0cc04001f80e403e00f
def ridgeSupport196_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport196_code
def ridgeSupport196_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport196_code
def ridgeSupport196_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport196_code
def ridgeSupport196_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport196_code
def ridgeSupport196_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport196_code
def ridgeSupport196_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport196_code
def ridgeSupport196_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport196_code
def ridgeSupport196_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport196_code
def ridgeSupport196_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport196_code
def ridgeSupport196_rest_009 : Nat := PackedRawNatGrowth.drop 3497 ridgeSupport196_code
def ridgeSupport196_suffix_009 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 269 ridgeSupport196_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
