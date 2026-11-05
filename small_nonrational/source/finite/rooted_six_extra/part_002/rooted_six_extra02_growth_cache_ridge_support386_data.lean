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
def ridgeSupport386_000 : List Nat := [12,34,44,50,53,56,138,139,142,143,146,147,210,211,214,215,218,219,247,248,249,252,253,258,259,264,266,309,310,314,316,317]
def ridgeSupport386_001 : List Nat := [321,323,324,326,531,535,536,537,538,540,541,548,550,596,597,598,601,602,603,605,610,612,653,654,655,656,657,658,687,691,692,693]
def ridgeSupport386_002 : List Nat := [694,696,697,704,706,752,753,754,757,758,759,761,766,768,771,775,776,777,778,780,781,788,790,836,837,838,841,842,843,845,850,852]
def ridgeSupport386_003 : List Nat := [855,858,859,860,863,864,865,867,872,873,875,876,1389,1391,1408,1410,1468,1469,1474,1475,1488,1489,1491,1494,1497,1500,1502,1503,1516,1517,1522,1523]
def ridgeSupport386_004 : List Nat := [1557,1559,1564,1565,1570,1571,1576,1578,1584,1585,1598,1599,1608,1609,1622,1623,1893,1895,1912,1914,1924,1925,1930,1931,1972,1973,1978,1979,1992,1993,1995,1998]
def ridgeSupport386_005 : List Nat := [2001,2004,2006,2007,2013,2015,2020,2021,2026,2027,2032,2034,2068,2069,2074,2075,2092,2093,2098,2099,2110,2112,2140,2142,2150,2151,2168,2169,2325,2327,2355,2357]
def ridgeSupport386_006 : List Nat := [2370,2371,2388,2389,2661,2663,2680,2682,2692,2693,2698,2699,2740,2741,2746,2747,2760,2761,2763,2766,2769,2772,2774,2775,2781,2783,2788,2789,2794,2795,2800,2802]
def ridgeSupport386_007 : List Nat := [2836,2837,2842,2843,2860,2861,2866,2867,2878,2880,2908,2910,2918,2919,2936,2937,3093,3095,3123,3125,3138,3139,3156,3157,3765,3767,3784,3786,3796,3797,3802,3803]
def ridgeSupport386_008 : List Nat := [3844,3845,3850,3851,3864,3865,3867,3870,3873,3876,3878,3879,3885,3887,3892,3893,3898,3899,3904,3906,3940,3941,3946,3947,3964,3965,3970,3971,4234,4236,4246,4248]
def ridgeSupport386_009 : List Nat := [4274,4275,4286,4287,4449,4451,4461,4463,4494,4495,4506,4507,4802,4803,4810,4811,5133,5135,5140,5142,5156,5158,5165,5167,5170,5172,5187,5189,5204,5206,5213,5215]
def ridgeSupport386_010 : List Nat := [5218,5220,5235,5237,5264,5266,5273,5275,5291,5293,5306,5308,5376,5377,5450,5451,5546,5547,5702,5703,5860,5861,5866,5867,5876,5878,5880,5881,5884,5887,5955,5958]
def ridgeSupport386_011 : List Nat := [5961,5964,5984,5986,5988,5989,5992,5995,6002,6003,6005,6007,6056,6058,6060,6061,6123,6126,6129,6132,6152,6154,6156,6157,6160,6163,6170,6171,6173,6175,6224,6226]
def ridgeSupport386_012 : List Nat := [6228,6229,6339,6342,6345,6348,6368,6370,6372,6373,6376,6379,6440,6441,6443,6445,6494,6496,6498,6499]
def ridgeSupport386_code : Nat := 0xcb1e58b2c195ec96e4af253928c75e3a31cb8e4c7163831998c9c63630f0ab854c29614303f81dc0de06b027810c06e033015808bfa5fc6fdd7ebbd6deb2f557a8bbbddd6ee7772bb5dda2ecb764bb15d82e99749ba35d0edff6fcb7cdbe2ded6f4b75dbaadcb6e4b23d91ab575aaaa5d52aa03500a5e52ea95b4aba4dd266925490a3ad1ce8c9462a2fd1768ad454a22d10e869432a17d0b684d424a0b505281f40d965cb2a5872c28cdc66a31f18e8b7c5b62c716185fc2fa1670b284c425a11908a7c1be09efaf7c7b5bda9ecaf647a13d01e76f3a79abcd1e5ef2d793bc99e48f2178f3c6de32f18785bc29e0af0476dbb69daaed47653b21d6eeb562ab151886c4261ab0cd82ec155bcade16ceb665af2d71680b3e599acc965ab2c58dac6962ab145792bc15d6aea572ab915beadd56bab595a8ad15672b2d592ac855daae956aab4545aa2950aa8453d29e14cea654aaa55128694249aa4cd22e91543ca1e10ce86642f217108083e419a0c905a82c40da06902a8143f91fc0fd67ea3f29f90fbe7dd3eb9f58fa87d13e71f2cf927c83dd9ee8f6a7b43c59e28f0a7843bd1de0ece76532b9958c9264831f98f8c6263031518a0c4662230e9870c2e6152f997c8bda5ec2ef9778bb85d92eb174cba25d02e19708b7a5bc2c11600ade56d1b60dac6d23681b18d846c035f1ae0d6c6b43571aa0d4869a34b1a50d2468c3451a20c5862830d1860c286123081838c0c6002fe17c8bdc5ec2f51790bc45e02c21600ae45702b615a8ad05662af1490a4452028f1470a344c826212e896c4b425912b09544a8226112087443821a10c886042e2130a3051028614109e84f027413609a842821010308103f41f80f907c03dc1b60da06b83581a60d2049824811e08e045822807003501900b004400c
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
def ridgeSupport386_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport386_code
def ridgeSupport386_rest_013 : Nat := PackedRawNatGrowth.drop 5252 ridgeSupport386_code
def ridgeSupport386_suffix_013 : List Nat := []
def ridgeSupport386_suffix_012 : List Nat := ridgeSupport386_012 ++ ridgeSupport386_suffix_013
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
    (PackedRawNatGrowth.readList 13 404 ridgeSupport386_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
