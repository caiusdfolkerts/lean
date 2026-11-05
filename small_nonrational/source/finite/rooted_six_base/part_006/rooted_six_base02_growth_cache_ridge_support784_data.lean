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
def ridgeSupport784_000 : List Nat := [62,76,92,95,96,923,924,925,928,929,934,935,940,942,944,945,946,949,950,955,956,961,963,1049,1050,1053,1054,1057,1058,1104,1105,1106]
def ridgeSupport784_001 : List Nat := [1109,1110,1115,1116,1121,1123,1125,1126,1127,1130,1131,1136,1137,1142,1144,1296,1300,1301,1302,1303,1305,1306,1313,1315,1317,1321,1322,1323,1324,1326,1327,1334]
def ridgeSupport784_002 : List Nat := [1336,1338,1339,1343,1344,1345,1346,1348,1349,1357,1359,1360,1362,3166,3168,3172,3174,3252,3253,3258,3259,3260,3261,3266,3267,3272,3274,3278,3280,3300,3301,3306]
def ridgeSupport784_003 : List Nat := [3307,3334,3336,3340,3342,3348,3349,3354,3355,3356,3357,3362,3363,3380,3381,3386,3387,3406,3408,3412,3414,3492,3493,3498,3499,3500,3501,3506,3507,3512,3514,3518]
def ridgeSupport784_004 : List Nat := [3520,3540,3541,3546,3547,3574,3576,3580,3582,3588,3589,3594,3595,3596,3597,3602,3603,3620,3621,3626,3627,3728,3729,3732,3733,4534,4536,4540,4542,4572,4573,4578]
def ridgeSupport784_005 : List Nat := [4579,4620,4621,4626,4627,4628,4629,4634,4635,4640,4642,4646,4648,4654,4656,4660,4662,4668,4669,4674,4675,4716,4717,4722,4723,4740,4741,4746,4747,4832,4833,4840]
def ridgeSupport784_006 : List Nat := [4841,4990,4992,5020,5022,5030,5031,5048,5049,5062,5064,5092,5094,5102,5103,5120,5121,6226,6228,6230,6232,6248,6249,6254,6255,6260,6262,6266,6268,6288,6289,6294]
def ridgeSupport784_007 : List Nat := [6295,6296,6297,6302,6303,6322,6324,6328,6330,6336,6337,6342,6343,6344,6345,6347,6348,6358,6360,6362,6364,6380,6381,6386,6387,6392,6394,6398,6400,6420,6421,6426]
def ridgeSupport784_008 : List Nat := [6427,6428,6429,6434,6435,6454,6456,6460,6462,6468,6469,6474,6475,6476,6477,6479,6480,6510,6511,7006,7008,7010,7012,7032,7033,7038,7039,7040,7041,7046,7047,7052]
def ridgeSupport784_009 : List Nat := [7054,7058,7060,7066,7068,7072,7074,7080,7081,7086,7087,7088,7089,7094,7095,7119,7120,7122,7123,7146,7147,7258,7260,7262,7263,7280,7281,7288,7290,7298,7299,7307]
def ridgeSupport784_010 : List Nat := [7309,7312,7314,7316,7317,7334,7335,7342,7344,7352,7353,7361,7363,7474,7476,7478,7480,7486,7488,7490,7492,7547,7549,7551,7553,7570,7572,7576,7578,7832,7833,7868]
def ridgeSupport784_011 : List Nat := [7869,8034,8035]
def ridgeSupport784_code : Nat := 0x7d8fec5ebdf5e7a67d31d9aecc7653b25d81ebff5f7af7d44ea17503a7dd38e9b74d3a65cc3e60f2e7971cb0e57729f94dc95e4a724b921c8de45f20f905c7ae3c71c78e1c5fe2f71738b5bebdf56f4f7a5bd0de7eedf76dbb1dd86ebf75dba9dd46e8b741b9cdcd6e53725b8edc66e1f70db81dc06dff6fdb79dbc6d936c5b60daf65bf2dd950ca7e53729994bca5651728993ec9e64e326d923c91647723991bc8d6457229900c7f63eb1f18f3c7963b71d98dcc6d63631ad8ccc65e3271918c7c6363071818bac5c62d316589fc4f6267131897c4b624712187cc3d61db0e986fc3761a70d1858c2b61530a5401a004fbe7dd3e69f24f2278d3b99dc4e9e74d39e9ce4e026fd2e99744b865c128b9454a1650927393949b64d924392148f647923691a48c245d228913488a44121b90d485642921390948364191e38f147763b91be8de46e236ce9574a3a45d20e2b7153895c48e137093835c18e0b7053815c08dfe6fe37e1becddb6ed3755ba8dc06df36e9b70db36d936b5b58dab6d53695b48d566aa3541a9cd3b69d34d5a68d236913475a38d1b68d3455a28d0e6863421a0cceb67533959c8cd06673329990cc366132f5978cbb65d32d5968c6663231818bc5522a8153ca9a5452a21508a8254029f94eca7453829b14bca5c52c29594a8a525252919484a3451928b9458a2a51428811e08ec47123811ac8d446723311948c646122e116c8ac45522911448a0422210907883a41a20c8f0c7823bc1dd8ed876a3b21d88ec075c3ac1d38e987423a01ce8e7073606002f817009803e
def ridgeSupport784_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport784_code
def ridgeSupport784_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport784_code
def ridgeSupport784_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport784_code
def ridgeSupport784_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport784_code
def ridgeSupport784_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport784_code
def ridgeSupport784_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport784_code
def ridgeSupport784_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport784_code
def ridgeSupport784_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport784_code
def ridgeSupport784_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport784_code
def ridgeSupport784_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport784_code
def ridgeSupport784_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport784_code
def ridgeSupport784_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport784_code
def ridgeSupport784_rest_012 : Nat := PackedRawNatGrowth.drop 4615 ridgeSupport784_code
def ridgeSupport784_suffix_012 : List Nat := []
def ridgeSupport784_suffix_011 : List Nat := ridgeSupport784_011 ++ ridgeSupport784_suffix_012
def ridgeSupport784_suffix_010 : List Nat := ridgeSupport784_010 ++ ridgeSupport784_suffix_011
def ridgeSupport784_suffix_009 : List Nat := ridgeSupport784_009 ++ ridgeSupport784_suffix_010
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
    (PackedRawNatGrowth.readList 13 355 ridgeSupport784_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
