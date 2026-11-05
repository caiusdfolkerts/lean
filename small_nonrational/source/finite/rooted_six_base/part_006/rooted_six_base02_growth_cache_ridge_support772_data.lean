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
def ridgeSupport772_000 : List Nat := [20,36,62,65,66,162,163,164,165,172,173,377,378,379,382,383,388,389,394,396,398,399,400,403,404,409,410,415,417,574,575,576]
def ridgeSupport772_001 : List Nat := [579,580,585,586,591,593,595,596,597,600,601,606,607,612,614,922,926,927,928,929,931,932,939,941,943,947,948,949,950,952,953,960]
def ridgeSupport772_002 : List Nat := [962,964,965,969,970,971,972,974,975,983,985,986,988,1630,1632,1636,1638,1716,1717,1722,1723,1724,1725,1730,1731,1736,1738,1742,1744,1764,1765,1770]
def ridgeSupport772_003 : List Nat := [1771,1798,1800,1804,1806,1812,1813,1818,1819,1820,1821,1826,1827,1844,1845,1850,1851,1870,1872,1876,1878,1956,1957,1962,1963,1964,1965,1970,1971,1976,1978,1982]
def ridgeSupport772_004 : List Nat := [1984,2004,2005,2010,2011,2038,2040,2044,2046,2052,2053,2058,2059,2060,2061,2066,2067,2084,2085,2090,2091,2260,2262,2272,2274,2288,2289,2300,2301,2332,2334,2344]
def ridgeSupport772_005 : List Nat := [2346,2360,2361,2372,2373,3190,3192,3196,3198,3228,3229,3234,3235,3276,3277,3282,3283,3284,3285,3290,3291,3296,3298,3302,3304,3310,3312,3316,3318,3324,3325,3330]
def ridgeSupport772_006 : List Nat := [3331,3372,3373,3378,3379,3396,3397,3402,3403,3726,3727,3738,3739,4830,4831,4838,4839,5266,5268,5270,5272,5288,5289,5294,5295,5300,5302,5306,5308,5328,5329,5334]
def ridgeSupport772_007 : List Nat := [5335,5336,5337,5342,5343,5362,5364,5368,5370,5376,5377,5382,5383,5384,5385,5387,5388,5398,5400,5402,5404,5420,5421,5426,5427,5432,5434,5438,5440,5460,5461,5466]
def ridgeSupport772_008 : List Nat := [5467,5468,5469,5474,5475,5494,5496,5500,5502,5508,5509,5514,5515,5516,5517,5519,5520,5636,5637,5644,5646,5648,5649,5656,5658,5672,5673,5684,5685,5690,5691,5698]
def ridgeSupport772_009 : List Nat := [5700,5702,5703,5710,5712,5726,5727,5738,5739,6238,6240,6242,6244,6264,6265,6270,6271,6272,6273,6278,6279,6284,6286,6290,6292,6298,6300,6304,6306,6312,6313,6318]
def ridgeSupport772_010 : List Nat := [6319,6320,6321,6326,6327,6351,6352,6354,6355,6508,6509,7144,7145,7378,7380,7382,7384,7390,7392,7394,7396,7412,7413,7418,7419,7475,7477,7479,7481,7640,7641,7676]
def ridgeSupport772_011 : List Nat := [7677,7842,7843]
def ridgeSupport772_code : Nat := 0x7a8fd45dfdefe7767bb1d39e9bf4d7a67cfbe7d73d79e9ce4e7173839bdcd8e6b73539a5be9df465b72d98d3c69634319f8b7c5b62c71618afc5762a71518a2c506273135894c49623b119887c43620710187fc3f61e70f1864c3161830bd66bb35597ecbd650b27591ec8d644b2158eec75635b1a58a6c5161ab0c5846c2160eb065816c09590ac7d636b1958bac55616b0957eabe55e2aed563ab15576ab955baad5556aa9540a9f54eaa71533a9954b6a5951ca8d5462a2d50ca85d426a11507a835406a014faa7c53d29e54dfa6f53669b14d7a6b53469a14bca5d52da9694afa5752a6951498a4b52529252e79734b7e5bce9b74d3a3dd1cd4b6a53515a88d3369934b5a58d0368133f59f8cf667a33c19dcce867333899c0cdb66d33559a8cd36693335998ca36513275938c7e63e31e18ec9454a224e527092a49424792388fd47e23c51e08e247023591a882b4152095048813409203501880b40520150087fe3fe1fe0fec7db3ed1f54fa87c03df1ee8f707b33d91eb4f587ab3d51e94f487563aa1d40e9c73b39d1cd4e687233911c74e3871b38d1c54e2870e3861c20e0c6eb3751b94dc86d03671b28d906c33611af4d786bb35d1ad4d686663321980cbc3dc1ed0f647ae3cf1e70f307963ca1e48f147883c21e00ee47703b61da8ed07663af1d68eac7483a31d08e8073e39e1cd09984c825f12f09644b025512a094c4a224f125092448824312008fc47c1a10cf86683321940c9864031e18e0c6062830a1840bf85f82f617a0bc82b41580a5052028c14404202080f8048014
def ridgeSupport772_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport772_code
def ridgeSupport772_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport772_code
def ridgeSupport772_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport772_code
def ridgeSupport772_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport772_code
def ridgeSupport772_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport772_code
def ridgeSupport772_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport772_code
def ridgeSupport772_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport772_code
def ridgeSupport772_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport772_code
def ridgeSupport772_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport772_code
def ridgeSupport772_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport772_code
def ridgeSupport772_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport772_code
def ridgeSupport772_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport772_code
def ridgeSupport772_rest_012 : Nat := PackedRawNatGrowth.drop 4615 ridgeSupport772_code
def ridgeSupport772_suffix_012 : List Nat := []
def ridgeSupport772_suffix_011 : List Nat := ridgeSupport772_011 ++ ridgeSupport772_suffix_012
def ridgeSupport772_suffix_010 : List Nat := ridgeSupport772_010 ++ ridgeSupport772_suffix_011
def ridgeSupport772_suffix_009 : List Nat := ridgeSupport772_009 ++ ridgeSupport772_suffix_010
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
    (PackedRawNatGrowth.readList 13 355 ridgeSupport772_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
