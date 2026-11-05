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
def ridgeSupport324_000 : List Nat := [16,32,58,63,65,114,115,116,117,124,125,334,336,338,340,342,347,348,350,353,376,377,381,383,384,388,390,391,393,531,533,535]
def ridgeSupport324_001 : List Nat := [537,539,544,545,547,550,573,574,578,580,581,585,587,588,590,881,883,885,886,888,890,891,895,900,924,925,926,929,930,931,933,938]
def ridgeSupport324_002 : List Nat := [940,965,967,968,970,971,973,975,976,978,979,983,984,1635,1637,1646,1651,1702,1703,1712,1713,1725,1728,1734,1735,1739,1741,1744,1745,1750,1751,1760]
def ridgeSupport324_003 : List Nat := [1761,1798,1799,1803,1805,1808,1809,1814,1819,1830,1831,1840,1841,1854,1855,1864,1865,1875,1877,1886,1891,1942,1943,1952,1953,1965,1968,1974,1975,1979,1981,1984]
def ridgeSupport324_004 : List Nat := [1985,1990,1991,2000,2001,2038,2039,2043,2045,2048,2049,2054,2059,2070,2071,2080,2081,2094,2095,2104,2105,2114,2119,2126,2131,2146,2147,2158,2159,2259,2261,2271]
def ridgeSupport324_005 : List Nat := [2273,2292,2293,2304,2305,3195,3197,3206,3211,3214,3215,3224,3225,3262,3263,3272,3273,3285,3288,3294,3295,3299,3301,3304,3305,3310,3311,3315,3317,3320,3321,3326]
def ridgeSupport324_006 : List Nat := [3331,3358,3359,3368,3369,3382,3383,3392,3393,3662,3663,3674,3675,4766,4767,4774,4775,5265,5268,5271,5275,5289,5292,5298,5299,5303,5305,5308,5309,5314,5315,5324]
def ridgeSupport324_007 : List Nat := [5325,5346,5347,5356,5357,5362,5363,5367,5369,5372,5373,5378,5383,5388,5389,5393,5395,5397,5400,5403,5407,5421,5424,5430,5431,5435,5437,5440,5441,5446,5447,5456]
def ridgeSupport324_008 : List Nat := [5457,5478,5479,5488,5489,5494,5495,5499,5501,5504,5505,5510,5515,5520,5521,5525,5527,5530,5531,5534,5539,5542,5543,5546,5551,5566,5567,5578,5579,5640,5641,5643]
def ridgeSupport324_009 : List Nat := [5645,5652,5653,5655,5657,5676,5677,5688,5689,6237,6240,6243,6247,6250,6251,6260,6261,6273,6276,6282,6283,6287,6289,6292,6293,6298,6299,6303,6305,6308,6309,6314]
def ridgeSupport324_010 : List Nat := [6319,6330,6331,6340,6341,6344,6346,6350,6351,6492,6493,7128,7129,7377,7380,7383,7387,7389,7392,7395,7399,7402,7403,7416,7417,7472,7477,7478,7482,7648,7649,7684]
def ridgeSupport324_011 : List Nat := [7685,7834,7835]
def ridgeSupport324_code : Nat := 0x7a6fd35e05f027787bc1d3ae9b74d7a61cf9e7c73af9d5ce7e71f3839bbcdbe6bf3539a3bd9dec65772b98cfc67632b1918c5c6262ef1758afc5562971498a1c4fe26f135895c4a624711f88bc456213103875c3a61af0d5867c31e1830bb639b1c58b6c59619b0bd856c2960db05d826c115cbae556feb7d5afad5569eb4d5a3acf566eb35597acad646b2158bac35606b0157dabdd5deaed571ab8559eacd551aa8551ea8d541aa054f6a77537a9b54c2a5b51fa8dd462a2b513a88d436a19507a8153f69f94f9a7bd3ce9e54eda76538e9c54cda66530e9854bda5e52e696f4b3a5952b295349ba4bd2529232a79534a7e53ce5b72d393dc9cd416a034dda6cd29694347da3cd0367f33e59f0cf5679b3bd9dcce967433959c6cdf66f33619aacc966432fd97cc9964c323d91cc8b64331f58f690148023d51e88e146fa3551a686f437218d0c4853427211d08483941c20bd05c821410205d02c80b40320050007fd3fd9fdcfec7d13e81f1cf8c7c13e01ef4f767b73db1ec0f5a7a13d01e5cf2c7633af1d54ea67493a41cfce7c7313981c9ce4c71b38b1c44e2070d3859c1ce0c6e13701b5cdac6d13681b34d966c73631b00d7a6b13581a9cd4c6733371994cc63d81eb8f4c7a43d01e78f347963ca1e40f1c78a3ac1d50e947463a21d08e7873a39c1c20dfc6f637a1bc0dd86ea3731b8893849824b124891448824211f08f444c223110888043621910b88544261890c386183081800bf85f42f21780b085782b815b0ab05502a41500a701f40f807503a01cc0e404101f80e8040010
def ridgeSupport324_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport324_code
def ridgeSupport324_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport324_code
def ridgeSupport324_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport324_code
def ridgeSupport324_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport324_code
def ridgeSupport324_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport324_code
def ridgeSupport324_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport324_code
def ridgeSupport324_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport324_code
def ridgeSupport324_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport324_code
def ridgeSupport324_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport324_code
def ridgeSupport324_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport324_code
def ridgeSupport324_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport324_code
def ridgeSupport324_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport324_code
def ridgeSupport324_rest_012 : Nat := PackedRawNatGrowth.drop 4615 ridgeSupport324_code
def ridgeSupport324_suffix_012 : List Nat := []
def ridgeSupport324_suffix_011 : List Nat := ridgeSupport324_011 ++ ridgeSupport324_suffix_012
def ridgeSupport324_suffix_010 : List Nat := ridgeSupport324_010 ++ ridgeSupport324_suffix_011
def ridgeSupport324_suffix_009 : List Nat := ridgeSupport324_009 ++ ridgeSupport324_suffix_010
def ridgeSupport324_suffix_008 : List Nat := ridgeSupport324_008 ++ ridgeSupport324_suffix_009
def ridgeSupport324_suffix_007 : List Nat := ridgeSupport324_007 ++ ridgeSupport324_suffix_008
def ridgeSupport324_suffix_006 : List Nat := ridgeSupport324_006 ++ ridgeSupport324_suffix_007
def ridgeSupport324_suffix_005 : List Nat := ridgeSupport324_005 ++ ridgeSupport324_suffix_006
def ridgeSupport324_suffix_004 : List Nat := ridgeSupport324_004 ++ ridgeSupport324_suffix_005
def ridgeSupport324_suffix_003 : List Nat := ridgeSupport324_003 ++ ridgeSupport324_suffix_004
def ridgeSupport324_suffix_002 : List Nat := ridgeSupport324_002 ++ ridgeSupport324_suffix_003
def ridgeSupport324_suffix_001 : List Nat := ridgeSupport324_001 ++ ridgeSupport324_suffix_002
def ridgeSupport324_suffix_000 : List Nat := ridgeSupport324_000 ++ ridgeSupport324_suffix_001
theorem ridgeSupport324_source : candidateSupports 324 =
    (PackedRawNatGrowth.readList 13 355 ridgeSupport324_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
