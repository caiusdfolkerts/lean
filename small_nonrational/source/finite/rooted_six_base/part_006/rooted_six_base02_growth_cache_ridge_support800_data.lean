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
def ridgeSupport800_000 : List Nat := [52,82,92,99,100,675,676,677,678,685,686,814,815,816,819,820,825,826,831,833,835,836,837,840,841,846,847,852,854,1049,1050,1051]
def ridgeSupport800_001 : List Nat := [1052,1059,1060,1188,1189,1190,1193,1194,1199,1200,1205,1207,1209,1210,1211,1214,1215,1220,1221,1226,1228,1297,1298,1299,1302,1303,1308,1309,1314,1316,1318,1319]
def ridgeSupport800_002 : List Nat := [1320,1323,1324,1329,1330,1335,1337,1363,1364,1368,1369,1370,1371,1373,1374,1382,1384,1385,1387,3742,3744,3748,3750,3828,3829,3834,3835,3836,3837,3842,3843,3848]
def ridgeSupport800_003 : List Nat := [3850,3854,3856,3876,3877,3882,3883,3910,3912,3916,3918,3924,3925,3930,3931,3932,3933,3938,3939,3956,3957,3962,3963,3982,3984,3988,3990,4068,4069,4074,4075,4076]
def ridgeSupport800_004 : List Nat := [4077,4082,4083,4088,4090,4094,4096,4116,4117,4122,4123,4150,4152,4156,4158,4164,4165,4170,4171,4172,4173,4178,4179,4196,4197,4202,4203,4372,4374,4384,4386,4400]
def ridgeSupport800_005 : List Nat := [4401,4412,4413,4444,4446,4456,4458,4472,4473,4484,4485,4510,4512,4516,4518,4596,4597,4602,4603,4604,4605,4610,4611,4616,4618,4622,4624,4644,4645,4650,4651,4678]
def ridgeSupport800_006 : List Nat := [4680,4684,4686,4692,4693,4698,4699,4700,4701,4706,4707,4724,4725,4730,4731,4828,4829,4836,4837,4996,4998,5008,5010,5024,5025,5036,5037,5068,5070,5080,5082,5096]
def ridgeSupport800_007 : List Nat := [5097,5108,5109,6514,6516,6518,6520,6536,6537,6542,6543,6548,6550,6554,6556,6576,6577,6582,6583,6584,6585,6590,6591,6610,6612,6616,6618,6624,6625,6630,6631,6632]
def ridgeSupport800_008 : List Nat := [6633,6635,6636,6646,6648,6650,6652,6668,6669,6674,6675,6680,6682,6686,6688,6708,6709,6714,6715,6716,6717,6722,6723,6742,6744,6748,6750,6756,6757,6762,6763,6764]
def ridgeSupport800_009 : List Nat := [6765,6767,6768,6884,6885,6892,6894,6896,6897,6904,6906,6920,6921,6932,6933,6938,6939,6946,6948,6950,6951,6958,6960,6974,6975,6986,6987,6994,6996,6998,7000,7016]
def ridgeSupport800_010 : List Nat := [7017,7022,7023,7028,7030,7034,7036,7056,7057,7062,7063,7064,7065,7070,7071,7090,7092,7096,7098,7104,7105,7110,7111,7112,7113,7115,7116,7144,7145,7256,7257,7264]
def ridgeSupport800_011 : List Nat := [7266,7268,7269,7276,7278,7292,7293,7304,7305,7310,7311,7318,7320,7322,7323,7330,7332,7346,7347,7358,7359,7498,7500,7502,7504,7510,7512,7514,7516,7532,7533,7538]
def ridgeSupport800_012 : List Nat := [7539,7546,7548,7550,7552,7568,7569,7574,7575,7928,7929,7964,7965,8024,8025]
def ridgeSupport800_code : Nat := 0x7d67eb1f1df8e7be7df1d97ecb7647b21d80ebf75f3af5d73eb975b7ad9d5cead7563aadd50ea77533a95cbfe5f72cf965ca4e51726f935c98e4b723f91dc89e4471f78f9c6ee3671978c9c62e3071678b1be9df46f33797bc9de46f1f78dbc1de06eeb771bb4dd96e7f73db99dcc6e5f72db91dc86df36f5b76dba6dbf6ddb69db46d636adb54da96d2f695b3fd9f6cc365db27d936c93645b1bd8d6c57629b09d846beb5f1af1d786bbb5d9ae5d7269c34dfa6dd3669af4d5a65d32697b4b9a58d2b690f485a3dd1e68ef475a35d1a688343da1ad0c684f425a0dd0667f33f59f8cfb67b33d79e9cf4679f3cd9e1cf0676b3b19d4ce966ff37d9b9cdc66df36d9b1cd86673335996cca663f31d989cc465e32ed974cb94fd67e93e99f44f6a7b13ce9e64eb67593a19d04e4a7213869c24b965c92dd96e49ee4f527593a498e4c525d92e496e4b525592a493a49924892348ae455225912484241d20a904480e4051fd8fe47ee3f51f58fa469a3491a08cf46163091798bc45aa2d115e8ae44f6279131898448a24111688a41ae0d5065832414e0a504d826412e09504582240fa07903881b406e03501580a4001ffcffa7fc3fcdfe4fed7f63fadfd4fe57f23e59f28f907c73dedef4f757ba3d8dec4f5d7ae3d6deb4f557aa3d39e98f487a33cade54f257923c41e1cf0a7843c0de04efd77e3beddf4ef577a3a99d48ea074f15acad25682b31578aba55b2ad1564ab05542a994e4a6e53229894b0a565282939498a4852228e9470a2e5162899448a224cc26513149884bf25f12ec9744b925b92d49604af25512a494c4a5252109084641c20d90688323561aa0d3c69c3491a40d146883431a08cfc67433919a0ccc66032f1970ab855a2a61528a9054606403181700a4034
def ridgeSupport800_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport800_code
def ridgeSupport800_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport800_code
def ridgeSupport800_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport800_code
def ridgeSupport800_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport800_code
def ridgeSupport800_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport800_code
def ridgeSupport800_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport800_code
def ridgeSupport800_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport800_code
def ridgeSupport800_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport800_code
def ridgeSupport800_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport800_code
def ridgeSupport800_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport800_code
def ridgeSupport800_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport800_code
def ridgeSupport800_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport800_code
def ridgeSupport800_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport800_code
def ridgeSupport800_rest_013 : Nat := PackedRawNatGrowth.drop 5187 ridgeSupport800_code
def ridgeSupport800_suffix_013 : List Nat := []
def ridgeSupport800_suffix_012 : List Nat := ridgeSupport800_012 ++ ridgeSupport800_suffix_013
def ridgeSupport800_suffix_011 : List Nat := ridgeSupport800_011 ++ ridgeSupport800_suffix_012
def ridgeSupport800_suffix_010 : List Nat := ridgeSupport800_010 ++ ridgeSupport800_suffix_011
def ridgeSupport800_suffix_009 : List Nat := ridgeSupport800_009 ++ ridgeSupport800_suffix_010
def ridgeSupport800_suffix_008 : List Nat := ridgeSupport800_008 ++ ridgeSupport800_suffix_009
def ridgeSupport800_suffix_007 : List Nat := ridgeSupport800_007 ++ ridgeSupport800_suffix_008
def ridgeSupport800_suffix_006 : List Nat := ridgeSupport800_006 ++ ridgeSupport800_suffix_007
def ridgeSupport800_suffix_005 : List Nat := ridgeSupport800_005 ++ ridgeSupport800_suffix_006
def ridgeSupport800_suffix_004 : List Nat := ridgeSupport800_004 ++ ridgeSupport800_suffix_005
def ridgeSupport800_suffix_003 : List Nat := ridgeSupport800_003 ++ ridgeSupport800_suffix_004
def ridgeSupport800_suffix_002 : List Nat := ridgeSupport800_002 ++ ridgeSupport800_suffix_003
def ridgeSupport800_suffix_001 : List Nat := ridgeSupport800_001 ++ ridgeSupport800_suffix_002
def ridgeSupport800_suffix_000 : List Nat := ridgeSupport800_000 ++ ridgeSupport800_suffix_001
theorem ridgeSupport800_source : candidateSupports 800 =
    (PackedRawNatGrowth.readList 13 399 ridgeSupport800_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
