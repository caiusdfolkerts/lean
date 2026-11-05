module
prelude
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport292_000 : List Nat := [67,77,86,88,90,1056,1059,1060,1063,1066,1080,1083,1084,1087,1090,1105,1106,1109,1110,1115,1212,1215,1216,1219,1222,1236,1239,1240,1243,1246,1261,1262]
def ridgeSupport292_001 : List Nat := [1265,1266,1271,1356,1357,1359,1360,1363,1364,1365,1367,1368,1370,1375,1376,1398,1400,1401,1403,1404,1406,1408,1409,1411,1412,1415,1416,1419,1421,1422,1424,1425]
def ridgeSupport292_002 : List Nat := [1427,1429,1430,1432,1433,1436,1437,5466,5467,5472,5473,5476,5477,5478,5479,5480,5481,5486,5487,5490,5491,5496,5497,5500,5501,5502,5503,5504,5505,5510,5511,5524]
def ridgeSupport292_003 : List Nat := [5525,5526,5527,5528,5529,5548,5549,5550,5551,5552,5553,5572,5573,5574,5575,5576,5577,5596,5597,5598,5599,5600,5601,5620,5621,5622,5623,5624,5625,5644,5645,5646]
def ridgeSupport292_004 : List Nat := [5647,5648,5649,5657,5660,5663,5666,5668,5669,5670,5671,5672,5673,5674,5676,5954,5955,5972,5973,5990,5991,5992,5994,5998,6000,6008,6009,6096,6097,6114,6115,6132]
def ridgeSupport292_005 : List Nat := [6133,6137,6140,6143,6146,6150,6151,6168,6169,6186,6187,6204,6205,6209,6212,6215,6218,6222,6223,6482,6483,6500,6501,6518,6519,6520,6522,6526,6528,6536,6537,6624]
def ridgeSupport292_006 : List Nat := [6625,6642,6643,6660,6661,6665,6668,6671,6674,6678,6679,6696,6697,6714,6715,6732,6733,6737,6740,6743,6746,6750,6751,7504,7505,7506,7507,7508,7509,8476,8477,8478]
def ridgeSupport292_007 : List Nat := [8479,8480,8481,8489,8492,8495,8497,8498,8499,8501,8504,8507,8509,8510,8511,8560,8562,8576,8577,8597,8600,8610,8611,8615,8618,8628,8629,8680,8682,8696,8697,8717]
def ridgeSupport292_008 : List Nat := [8720,8730,8731,8735,8738,8748,8749]
def ridgeSupport292_code : Nat := 0x222d88b2222887e21b886a21088361f987e21ea87a21b586d21aa869e1a3868a1988656181860217285c213f84fa13d84ee13884d613384ca13184be12c84a6121848211f847a11d8471d557551d537549d517541a5f6979a5a695da546945a4d6931a3b68e9a2968a1a176859a12683da0c6825a0568119f367c99e16781989662198065f997a65e197765d99656591953654984f613984a611d844610583d60f182b60a9819606180760198025ffd7fc5fe57f55fd17e35f897d15f417795de17705db976a5da17675d997555d517435d0962c58a962958a162758996255891622587d61c5865611584160f583960d58315f957e15f757d95f557d15e157815df57795dd57715c957215c757195c557115b156c15af56b95ad56b15995661597565959556515875619581560157f55f957d55f157955e157355c956f55b956955a156755995655591561558155b556859d1670599166059616545931644590163858d162c588161c584160c581160057e15f057b15e457815d8560157c55a15605571554554154c550153c54d15304f713c84f113b84ed13784db13604d713504c6130c4c012fc4bc116c4561154452114444210fc43c10ec43810a84271090423108005a01600560134043
def ridgeSupport292_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport292_code
def ridgeSupport292_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport292_code
def ridgeSupport292_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport292_code
def ridgeSupport292_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport292_code
def ridgeSupport292_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport292_code
def ridgeSupport292_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport292_code
def ridgeSupport292_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport292_code
def ridgeSupport292_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport292_code
def ridgeSupport292_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport292_code
def ridgeSupport292_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport292_code
def ridgeSupport292_suffix_009 : List Nat := []
def ridgeSupport292_suffix_008 : List Nat := ridgeSupport292_008 ++ ridgeSupport292_suffix_009
def ridgeSupport292_suffix_007 : List Nat := ridgeSupport292_007 ++ ridgeSupport292_suffix_008
def ridgeSupport292_suffix_006 : List Nat := ridgeSupport292_006 ++ ridgeSupport292_suffix_007
def ridgeSupport292_suffix_005 : List Nat := ridgeSupport292_005 ++ ridgeSupport292_suffix_006
def ridgeSupport292_suffix_004 : List Nat := ridgeSupport292_004 ++ ridgeSupport292_suffix_005
def ridgeSupport292_suffix_003 : List Nat := ridgeSupport292_003 ++ ridgeSupport292_suffix_004
def ridgeSupport292_suffix_002 : List Nat := ridgeSupport292_002 ++ ridgeSupport292_suffix_003
def ridgeSupport292_suffix_001 : List Nat := ridgeSupport292_001 ++ ridgeSupport292_suffix_002
def ridgeSupport292_suffix_000 : List Nat := ridgeSupport292_000 ++ ridgeSupport292_suffix_001
theorem ridgeSupport292_source : candidateSupports 292 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport292_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
