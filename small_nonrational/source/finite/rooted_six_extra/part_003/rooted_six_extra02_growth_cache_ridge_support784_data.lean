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
def ridgeSupport784_000 : List Nat := [62,76,92,95,96,923,924,925,928,929,934,935,940,942,944,945,946,949,950,955,956,961,963,1049,1050,1053,1054,1057,1058,1104,1105,1106]
def ridgeSupport784_001 : List Nat := [1109,1110,1115,1116,1121,1123,1125,1126,1127,1130,1131,1136,1137,1142,1144,1296,1300,1301,1302,1303,1305,1306,1313,1315,1317,1321,1322,1323,1324,1326,1327,1334]
def ridgeSupport784_002 : List Nat := [1336,1338,1339,1343,1344,1345,1346,1348,1349,1357,1359,1360,1362,3166,3168,3172,3174,3252,3253,3258,3259,3260,3261,3266,3267,3272,3274,3278,3280,3300,3301,3306]
def ridgeSupport784_003 : List Nat := [3307,3334,3336,3340,3342,3348,3349,3354,3355,3356,3357,3362,3363,3380,3381,3386,3387,3406,3408,3412,3414,3492,3493,3498,3499,3500,3501,3506,3507,3512,3514,3518]
def ridgeSupport784_004 : List Nat := [3520,3540,3541,3546,3547,3574,3576,3580,3582,3588,3589,3594,3595,3596,3597,3602,3603,3620,3621,3626,3627,3728,3729,3732,3733,4534,4536,4540,4542,4572,4573,4578]
def ridgeSupport784_005 : List Nat := [4579,4620,4621,4626,4627,4628,4629,4634,4635,4640,4642,4646,4648,4654,4656,4660,4662,4668,4669,4674,4675,4716,4717,4722,4723,4740,4741,4746,4747,4832,4833,4840]
def ridgeSupport784_006 : List Nat := [4841,4990,4992,5020,5022,5030,5031,5048,5049,5062,5064,5092,5094,5102,5103,5120,5121,5242,5244,5246,5248,5254,5256,5258,5260,5315,5317,5319,5321,5338,5340,5344]
def ridgeSupport784_007 : List Nat := [5346,5600,5601,5636,5637,5802,5803,6252,6253,6258,6259,6260,6261,6263,6265,6266,6267,6300,6301,6306,6307,6308,6309,6311,6313,6314,6315,6512,6514,6518,6520,6536]
def ridgeSupport784_008 : List Nat := [6537,6539,6541,6542,6543,6590,6591,6593,6595,6608,6609,6611,6613]
def ridgeSupport784_code : Nat := 0x19d5ce9e7473a19c3ce0e6ff37d98fcc76637317989cc465e32ed972cb862af1558a9c53e2971498a3c51627713987bc3d61e70ef875c3a61cf0e586dc365aaed55605b025786bc14e2a7053729b54c9a63d31698748ca45522290d480a3f51f28f5401a004fbe7dd3e69f24f2278d3b99dc4e9e74d39e9ce4e026fd2e99744b865c128b9454a1650927393949b64d924392148f647923691a48c245d228913488a44121b90d485642921390948364191e38f147763b91be8de46e236ce9574a3a45d20e2b7153895c48e137093835c18e0b7053815c08dfe6fe37e1becddb6ed3755ba8dc06df36e9b70db36d936b5b58dab6d53695b48d566aa3541a9cd3b69d34d5a68d236913475a38d1b68d3455a28d0e6863421a0cceb67533959c8cd06673329990cc366132f5978cbb65d32d5968c6663231818bc5522a8153ca9a5452a21508a8254029f94eca7453829b14bca5c52c29594a8a525252919484a3451928b9458a2a51428811e08ec47123811ac8d446723311948c646122e116c8ac45522911448a0422210907883a41a20c8f0c7823bc1dd8ed876a3b21d88ec075c3ac1d38e987423a01ce8e7073606002f817009803e
def ridgeSupport784_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport784_code
def ridgeSupport784_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport784_code
def ridgeSupport784_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport784_code
def ridgeSupport784_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport784_code
def ridgeSupport784_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport784_code
def ridgeSupport784_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport784_code
def ridgeSupport784_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport784_code
def ridgeSupport784_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport784_code
def ridgeSupport784_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport784_code
def ridgeSupport784_rest_009 : Nat := PackedRawNatGrowth.drop 3497 ridgeSupport784_code
def ridgeSupport784_suffix_009 : List Nat := []
def ridgeSupport784_suffix_008 : List Nat := ridgeSupport784_008 ++ ridgeSupport784_suffix_009
def ridgeSupport784_suffix_007 : List Nat := ridgeSupport784_007 ++ ridgeSupport784_suffix_008
def ridgeSupport784_suffix_006 : List Nat := ridgeSupport784_006 ++ ridgeSupport784_suffix_007
def ridgeSupport784_suffix_005 : List Nat := ridgeSupport784_005 ++ ridgeSupport784_suffix_006
def ridgeSupport784_suffix_004 : List Nat := ridgeSupport784_004 ++ ridgeSupport784_suffix_005
def ridgeSupport784_suffix_003 : List Nat := ridgeSupport784_003 ++ ridgeSupport784_suffix_004
def ridgeSupport784_suffix_002 : List Nat := ridgeSupport784_002 ++ ridgeSupport784_suffix_003
def ridgeSupport784_suffix_001 : List Nat := ridgeSupport784_001 ++ ridgeSupport784_suffix_002
def ridgeSupport784_suffix_000 : List Nat := ridgeSupport784_000 ++ ridgeSupport784_suffix_001
theorem ridgeSupport784_source : candidateSupports 784 =
    (PackedRawNatGrowth.readList 13 269 ridgeSupport784_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
