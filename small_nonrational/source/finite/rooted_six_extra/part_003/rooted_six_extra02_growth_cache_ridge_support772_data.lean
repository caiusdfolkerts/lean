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
def ridgeSupport772_000 : List Nat := [20,36,62,65,66,162,163,164,165,172,173,377,378,379,382,383,388,389,394,396,398,399,400,403,404,409,410,415,417,574,575,576]
def ridgeSupport772_001 : List Nat := [579,580,585,586,591,593,595,596,597,600,601,606,607,612,614,922,926,927,928,929,931,932,939,941,943,947,948,949,950,952,953,960]
def ridgeSupport772_002 : List Nat := [962,964,965,969,970,971,972,974,975,983,985,986,988,1630,1632,1636,1638,1716,1717,1722,1723,1724,1725,1730,1731,1736,1738,1742,1744,1764,1765,1770]
def ridgeSupport772_003 : List Nat := [1771,1798,1800,1804,1806,1812,1813,1818,1819,1820,1821,1826,1827,1844,1845,1850,1851,1870,1872,1876,1878,1956,1957,1962,1963,1964,1965,1970,1971,1976,1978,1982]
def ridgeSupport772_004 : List Nat := [1984,2004,2005,2010,2011,2038,2040,2044,2046,2052,2053,2058,2059,2060,2061,2066,2067,2084,2085,2090,2091,2260,2262,2272,2274,2288,2289,2300,2301,2332,2334,2344]
def ridgeSupport772_005 : List Nat := [2346,2360,2361,2372,2373,3190,3192,3196,3198,3228,3229,3234,3235,3276,3277,3282,3283,3284,3285,3290,3291,3296,3298,3302,3304,3310,3312,3316,3318,3324,3325,3330]
def ridgeSupport772_006 : List Nat := [3331,3372,3373,3378,3379,3396,3397,3402,3403,3726,3727,3738,3739,4830,4831,4838,4839,5146,5148,5150,5152,5158,5160,5162,5164,5180,5181,5186,5187,5243,5245,5247]
def ridgeSupport772_007 : List Nat := [5249,5408,5409,5444,5445,5610,5611,5916,5917,5922,5923,5924,5925,5927,5929,5930,5931,5964,5965,5970,5971,5972,5973,5975,5977,5978,5979,6032,6033,6035,6037,6050]
def ridgeSupport772_008 : List Nat := [6051,6053,6055,6248,6250,6254,6256,6272,6273,6275,6277,6278,6279]
def ridgeSupport772_code : Nat := 0x1887c436217107881c4061c30dd86ac345e9ef4b7a3bd15e56f27791bc85d6eeb5759babdd56ea9753ba95d36e9972bb955ca6e4f725b925c8ee4571db8e57aebd5545aa25486a41481a3fd1f68f7443a2150f687942ca1550a284d420a0f50728352e79734b7e5bce9b74d3a3dd1cd4b6a53515a88d3369934b5a58d0368133f59f8cf667a33c19dcce867333899c0cdb66d33559a8cd36693335998ca36513275938c7e63e31e18ec9454a224e527092a49424792388fd47e23c51e08e247023591a882b4152095048813409203501880b40520150087fe3fe1fe0fec7db3ed1f54fa87c03df1ee8f707b33d91eb4f587ab3d51e94f487563aa1d40e9c73b39d1cd4e687233911c74e3871b38d1c54e2870e3861c20e0c6eb3751b94dc86d03671b28d906c33611af4d786bb35d1ad4d686663321980cbc3dc1ed0f647ae3cf1e70f307963ca1e48f147883c21e00ee47703b61da8ed07663af1d68eac7483a31d08e8073e39e1cd09984c825f12f09644b025512a094c4a224f125092448824312008fc47c1a10cf86683321940c9864031e18e0c6062830a1840bf85f82f617a0bc82b41580a5052028c14404202080f8048014
def ridgeSupport772_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport772_code
def ridgeSupport772_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport772_code
def ridgeSupport772_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport772_code
def ridgeSupport772_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport772_code
def ridgeSupport772_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport772_code
def ridgeSupport772_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport772_code
def ridgeSupport772_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport772_code
def ridgeSupport772_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport772_code
def ridgeSupport772_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport772_code
def ridgeSupport772_rest_009 : Nat := PackedRawNatGrowth.drop 3497 ridgeSupport772_code
def ridgeSupport772_suffix_009 : List Nat := []
def ridgeSupport772_suffix_008 : List Nat := ridgeSupport772_008 ++ ridgeSupport772_suffix_009
def ridgeSupport772_suffix_007 : List Nat := ridgeSupport772_007 ++ ridgeSupport772_suffix_008
def ridgeSupport772_suffix_006 : List Nat := ridgeSupport772_006 ++ ridgeSupport772_suffix_007
def ridgeSupport772_suffix_005 : List Nat := ridgeSupport772_005 ++ ridgeSupport772_suffix_006
def ridgeSupport772_suffix_004 : List Nat := ridgeSupport772_004 ++ ridgeSupport772_suffix_005
def ridgeSupport772_suffix_003 : List Nat := ridgeSupport772_003 ++ ridgeSupport772_suffix_004
def ridgeSupport772_suffix_002 : List Nat := ridgeSupport772_002 ++ ridgeSupport772_suffix_003
def ridgeSupport772_suffix_001 : List Nat := ridgeSupport772_001 ++ ridgeSupport772_suffix_002
def ridgeSupport772_suffix_000 : List Nat := ridgeSupport772_000 ++ ridgeSupport772_suffix_001
theorem ridgeSupport772_source : candidateSupports 772 =
    (PackedRawNatGrowth.readList 13 269 ridgeSupport772_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
