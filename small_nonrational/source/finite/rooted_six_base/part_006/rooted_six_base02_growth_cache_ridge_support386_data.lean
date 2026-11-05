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
def ridgeSupport386_000 : List Nat := [12,34,44,50,53,56,138,139,142,143,146,147,210,211,214,215,218,219,247,248,249,252,253,258,259,264,266,309,310,314,316,317]
def ridgeSupport386_001 : List Nat := [321,323,324,326,531,535,536,537,538,540,541,548,550,596,597,598,601,602,603,605,610,612,653,654,655,656,657,658,687,691,692,693]
def ridgeSupport386_002 : List Nat := [694,696,697,704,706,752,753,754,757,758,759,761,766,768,771,775,776,777,778,780,781,788,790,836,837,838,841,842,843,845,850,852]
def ridgeSupport386_003 : List Nat := [855,858,859,860,863,864,865,867,872,873,875,876,1389,1391,1408,1410,1468,1469,1474,1475,1488,1489,1491,1494,1497,1500,1502,1503,1516,1517,1522,1523]
def ridgeSupport386_004 : List Nat := [1557,1559,1564,1565,1570,1571,1576,1578,1584,1585,1598,1599,1608,1609,1622,1623,1893,1895,1912,1914,1924,1925,1930,1931,1972,1973,1978,1979,1992,1993,1995,1998]
def ridgeSupport386_005 : List Nat := [2001,2004,2006,2007,2013,2015,2020,2021,2026,2027,2032,2034,2068,2069,2074,2075,2092,2093,2098,2099,2110,2112,2140,2142,2150,2151,2168,2169,2325,2327,2355,2357]
def ridgeSupport386_006 : List Nat := [2370,2371,2388,2389,2661,2663,2680,2682,2692,2693,2698,2699,2740,2741,2746,2747,2760,2761,2763,2766,2769,2772,2774,2775,2781,2783,2788,2789,2794,2795,2800,2802]
def ridgeSupport386_007 : List Nat := [2836,2837,2842,2843,2860,2861,2866,2867,2878,2880,2908,2910,2918,2919,2936,2937,3093,3095,3123,3125,3138,3139,3156,3157,3765,3767,3784,3786,3796,3797,3802,3803]
def ridgeSupport386_008 : List Nat := [3844,3845,3850,3851,3864,3865,3867,3870,3873,3876,3878,3879,3885,3887,3892,3893,3898,3899,3904,3906,3940,3941,3946,3947,3964,3965,3970,3971,4234,4236,4246,4248]
def ridgeSupport386_009 : List Nat := [4274,4275,4286,4287,4449,4451,4461,4463,4494,4495,4506,4507,4802,4803,4810,4811,5133,5135,5140,5142,5160,5161,5163,5166,5169,5172,5174,5175,5188,5189,5194,5195]
def ridgeSupport386_010 : List Nat := [5208,5209,5222,5223,5229,5231,5236,5237,5242,5243,5248,5250,5253,5254,5261,5262,5409,5411,5416,5418,5428,5429,5434,5435,5448,5449,5451,5454,5457,5460,5462,5463]
def ridgeSupport386_011 : List Nat := [5469,5471,5476,5477,5482,5483,5488,5490,5496,5497,5510,5511,5519,5521,5522,5524,5530,5532,5534,5535,5552,5553,5560,5562,5570,5571,5579,5581,5691,5693,5700,5701]
def ridgeSupport386_012 : List Nat := [5718,5719,5721,5723,5736,5737,5738,5740,5889,5891,5896,5898,5908,5909,5914,5915,5928,5929,5931,5934,5937,5940,5942,5943,5949,5951,5956,5957,5962,5963,5968,5970]
def ridgeSupport386_013 : List Nat := [5976,5977,5990,5991,5999,6001,6002,6004,6010,6012,6014,6015,6032,6033,6040,6042,6050,6051,6059,6061,6171,6173,6180,6181,6198,6199,6201,6203,6216,6217,6218,6220]
def ridgeSupport386_014 : List Nat := [6525,6527,6532,6534,6544,6545,6550,6551,6564,6565,6567,6570,6573,6576,6578,6579,6585,6587,6592,6593,6598,6599,6604,6606,6612,6613,6626,6627,6635,6637,6638,6640]
def ridgeSupport386_015 : List Nat := [6790,6792,6794,6795,6802,6804,6806,6807,6815,6817,6821,6823,6951,6953,6960,6961,6963,6965,6972,6973,6974,6976,6980,6982,7138,7139,7365,7367,7372,7374,7388,7390]
def ridgeSupport386_016 : List Nat := [7397,7399,7402,7404,7419,7421,7436,7438,7445,7447,7450,7452,7467,7469,7496,7498,7505,7507,7523,7525,7538,7540,7608,7609,7682,7683,7778,7779,7934,7935]
def ridgeSupport386_code : Nat := 0x3dffefef31f98bc07e02edcf6e3ae9d72eb2f58faa7d51ea57523a5bd2be8e746ba2fd15e8774339fbcfbe7673ab9cfce5e6f737399dccce63f3177c7be2da36d13681b3ed9eecf366bb33d98ecc3653b27d53ea97543a9fd4bea5b529a92d45ea2b511a86cf867bb3db9ebcf1e78b3ab9d4ce7673338f9c6ce0e7033779b9cd9e6cb3619adcd5669f34b9a4ccbe65b323990cc366132ff97dc26612b093848c1de0e706f836c12e09303b81bbd6deaef477a2bcd5e62f23790bbfddfaef977abba5dcaee376fbb3dd9aeb3758ba95d42e9774aba2dd12e7f73db9bdcdae69731b975caee53728b8ddc6ae2b714b855c22e07701b3659aacd3668b2dd966caf656b22d912c7b63bae6d72eb875c2add56e2b635b0acfd67ab3959aaca564ab2358fac3d61aaf3578ab955c2ad756aab2d592abf55daabd55aaa9551aa7552ea93548a9dd4eaa6b534a9554a2a47521a47523690d485a4152028f747aa3ad1d28df46da33d19a8b3458a25d12a88b444a1bd0da869431a1750ae853428a0b505281f40d965cb2a5872c28cdc66a31f18e8b7c5b62c716185fc2fa1670b284c425a11908a7c1be09efaf7c7b5bda9ecaf647a13d01e76f3a79abcd1e5ef2d793bc99e48f2178f3c6de32f18785bc29e0af0476dbb69daaed47653b21d6eeb562ab151886c4261ab0cd82ec155bcade16ceb665af2d71680b3e599acc965ab2c58dac6962ab145792bc15d6aea572ab915beadd56bab595a8ad15672b2d592ac855daae956aab4545aa2950aa8453d29e14cea654aaa55128694249aa4cd22e91543ca1e10ce86642f217108083e419a0c905a82c40da06902a8143f91fc0fd67ea3f29f90fbe7dd3eb9f58fa87d13e71f2cf927c83dd9ee8f6a7b43c59e28f0a7843bd1de0ece76532b9958c9264831f98f8c6263031518a0c4662230e9870c2e6152f997c8bda5ec2ef9778bb85d92eb174cba25d02e19708b7a5bc2c11600ade56d1b60dac6d23681b18d846c035f1ae0d6c6b43571aa0d4869a34b1a50d2468c3451a20c5862830d1860c286123081838c0c6002fe17c8bdc5ec2f51790bc45e02c21600ae45702b615a8ad05662af1490a4452028f1470a344c826212e896c4b425912b09544a8226112087443821a10c886042e2130a3051028614109e84f027413609a842821010308103f41f80f907c03dc1b60da06b83581a60d2049824811e08e045822807003501900b004400c
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
def ridgeSupport386_rest_013 : Nat := PackedRawNatGrowth.drop 5408 ridgeSupport386_code
def ridgeSupport386_rest_014 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport386_code
def ridgeSupport386_rest_015 : Nat := PackedRawNatGrowth.drop 6240 ridgeSupport386_code
def ridgeSupport386_rest_016 : Nat := PackedRawNatGrowth.drop 6656 ridgeSupport386_code
def ridgeSupport386_rest_017 : Nat := PackedRawNatGrowth.drop 7046 ridgeSupport386_code
def ridgeSupport386_suffix_017 : List Nat := []
def ridgeSupport386_suffix_016 : List Nat := ridgeSupport386_016 ++ ridgeSupport386_suffix_017
def ridgeSupport386_suffix_015 : List Nat := ridgeSupport386_015 ++ ridgeSupport386_suffix_016
def ridgeSupport386_suffix_014 : List Nat := ridgeSupport386_014 ++ ridgeSupport386_suffix_015
def ridgeSupport386_suffix_013 : List Nat := ridgeSupport386_013 ++ ridgeSupport386_suffix_014
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
    (PackedRawNatGrowth.readList 13 542 ridgeSupport386_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
