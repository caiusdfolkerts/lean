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
def ridgeSupport224_000 : List Nat := [47,77,87,97,98,615,616,617,618,625,626,771,772,776,778,779,783,785,786,788,792,793,797,799,800,804,806,807,809,989,990,991]
def ridgeSupport224_001 : List Nat := [992,999,1000,1145,1146,1150,1152,1153,1157,1159,1160,1162,1166,1167,1171,1173,1174,1178,1180,1181,1183,1254,1255,1259,1261,1262,1266,1268,1269,1271,1275,1276]
def ridgeSupport224_002 : List Nat := [1280,1282,1283,1287,1289,1290,1292,1365,1366,1368,1369,1370,1371,1373,1374,1376,1377,1379,1380,3753,3755,3759,3761,3812,3813,3818,3819,3839,3841,3845,3847,3852]
def ridgeSupport224_003 : List Nat := [3853,3858,3859,3860,3861,3866,3867,3908,3909,3914,3915,3921,3923,3927,3929,3948,3949,3954,3955,3972,3973,3978,3979,3993,3995,3999,4001,4052,4053,4058,4059,4079]
def ridgeSupport224_004 : List Nat := [4081,4085,4087,4092,4093,4098,4099,4100,4101,4106,4107,4148,4149,4154,4155,4161,4163,4167,4169,4188,4189,4194,4195,4212,4213,4218,4219,4227,4229,4239,4241,4260]
def ridgeSupport224_005 : List Nat := [4261,4272,4273,4299,4301,4311,4313,4332,4333,4344,4345,4521,4523,4527,4529,4580,4581,4586,4587,4607,4609,4613,4615,4620,4621,4626,4627,4628,4629,4634,4635,4676]
def ridgeSupport224_006 : List Nat := [4677,4682,4683,4689,4691,4695,4697,4716,4717,4722,4723,4740,4741,4746,4747,4748,4749,4756,4757,4851,4853,4863,4865,4884,4885,4896,4897,4923,4925,4935,4937,4956]
def ridgeSupport224_007 : List Nat := [4957,4968,4969,6515,6517,6519,6521,6539,6541,6545,6547,6552,6553,6558,6559,6560,6561,6566,6567,6600,6601,6606,6607,6608,6609,6614,6615,6621,6623,6627,6629,6639]
def ridgeSupport224_008 : List Nat := [6640,6642,6643,6647,6649,6651,6653,6671,6673,6677,6679,6684,6685,6690,6691,6692,6693,6698,6699,6732,6733,6738,6739,6740,6741,6746,6747,6753,6755,6759,6761,6771]
def ridgeSupport224_009 : List Nat := [6772,6774,6775,6780,6781,6783,6785,6792,6793,6795,6797,6816,6817,6828,6829,6834,6835,6837,6839,6846,6847,6849,6851,6870,6871,6882,6883,6995,6997,6999,7001,7019]
def ridgeSupport224_010 : List Nat := [7021,7025,7027,7032,7033,7038,7039,7040,7041,7046,7047,7080,7081,7086,7087,7088,7089,7094,7095,7101,7103,7107,7109,7119,7120,7122,7123,7124,7125,7152,7153,7155]
def ridgeSupport224_011 : List Nat := [7157,7164,7165,7167,7169,7188,7189,7200,7201,7206,7207,7209,7211,7218,7219,7221,7223,7242,7243,7254,7255,7499,7501,7503,7505,7511,7513,7515,7517,7524,7525,7530]
def ridgeSupport224_012 : List Nat := [7531,7547,7549,7551,7553,7560,7561,7566,7567,7938,7939,7974,7975,8034,8035]
def ridgeSupport224_code : Nat := 0x7d8fec5f27f937c0fe05d8fec77627b11d81ebff5f7af7d6beb57597ac9d5deadf567aafd51ea7f537a97c57e2b712f895c37e1af0cf865c2be14f09f84dc21e107057829c01dffeff77f9bf5df9efc77e1bd5dea6f4f7a5bd0de7ef17787bbfddeeedf76dbb1dd86ebf75dba9dd46e1f70db81dc06dff6fdb79dbc6dcf6e3b6ddb5ed676afb55da9eb8f5c5ad7d6b6b0f583abfd5f6adf56bab3d596ab7559aa1d506a37517a89d446a074ffa7dd3e69df4eda74d39e9a74cfa63d30e96f4b5a55d2a694f4a5a4dd2668af455a25d12688f445a1dd0e685f42ba11d07e7f73f79f9cfbe7cf3e59f0cf7e7973c79dfceee75f3ad9d1ce8673f39d9c9ce4669f34d9a1cd0667f33d999ccc664f32398dcc5e5e72ef975cb9cda66d135d9ae4d2668f33d99dcc8664131598a4c065ff2f5979ca5652928d9464a2e51528594249ce4e526d93649664af253928c92e495245922486e43521590a484e42520d906481e40b2018ffc7ae3d51e58f246c635f1ab8d4c3e61f10ed87643661af0cd865c2c61610a5852424611f085841c1ee0f507583a418e0c505d82e412608f043820c0ee07503581a402e015005802400e004ffd7fe3fddfeaff17f7bf6dfb4fd57ea3e85f3ef9b7ccbe2df14f857c23dcdee4f6d7b63d65eaef537a8bd2de94f457a23c6de34f1578a3c4de24f0d7863c1de0af0177fbbaddd4ee57723ac5d5eeab7549590ac65612b01578aba55b2ad1564ab05562aa9430a14509283940ca0450027e13ec9ee4f527a13c89dc4ed275939c9cc49f24e927093449624a924c91e48e245122090e48524092008fc47a23c8fa07ce3e01ef8f787ba3291938c9864832018f8c7463231818a0c4862230f1858c2861030418189c84e226a13489a04ce062030815c09a02f
def ridgeSupport224_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport224_code
def ridgeSupport224_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport224_code
def ridgeSupport224_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport224_code
def ridgeSupport224_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport224_code
def ridgeSupport224_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport224_code
def ridgeSupport224_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport224_code
def ridgeSupport224_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport224_code
def ridgeSupport224_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport224_code
def ridgeSupport224_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport224_code
def ridgeSupport224_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport224_code
def ridgeSupport224_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport224_code
def ridgeSupport224_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport224_code
def ridgeSupport224_rest_012 : Nat := PackedRawNatGrowth.drop 4992 ridgeSupport224_code
def ridgeSupport224_rest_013 : Nat := PackedRawNatGrowth.drop 5187 ridgeSupport224_code
def ridgeSupport224_suffix_013 : List Nat := []
def ridgeSupport224_suffix_012 : List Nat := ridgeSupport224_012 ++ ridgeSupport224_suffix_013
def ridgeSupport224_suffix_011 : List Nat := ridgeSupport224_011 ++ ridgeSupport224_suffix_012
def ridgeSupport224_suffix_010 : List Nat := ridgeSupport224_010 ++ ridgeSupport224_suffix_011
def ridgeSupport224_suffix_009 : List Nat := ridgeSupport224_009 ++ ridgeSupport224_suffix_010
def ridgeSupport224_suffix_008 : List Nat := ridgeSupport224_008 ++ ridgeSupport224_suffix_009
def ridgeSupport224_suffix_007 : List Nat := ridgeSupport224_007 ++ ridgeSupport224_suffix_008
def ridgeSupport224_suffix_006 : List Nat := ridgeSupport224_006 ++ ridgeSupport224_suffix_007
def ridgeSupport224_suffix_005 : List Nat := ridgeSupport224_005 ++ ridgeSupport224_suffix_006
def ridgeSupport224_suffix_004 : List Nat := ridgeSupport224_004 ++ ridgeSupport224_suffix_005
def ridgeSupport224_suffix_003 : List Nat := ridgeSupport224_003 ++ ridgeSupport224_suffix_004
def ridgeSupport224_suffix_002 : List Nat := ridgeSupport224_002 ++ ridgeSupport224_suffix_003
def ridgeSupport224_suffix_001 : List Nat := ridgeSupport224_001 ++ ridgeSupport224_suffix_002
def ridgeSupport224_suffix_000 : List Nat := ridgeSupport224_000 ++ ridgeSupport224_suffix_001
theorem ridgeSupport224_source : candidateSupports 224 =
    (PackedRawNatGrowth.readList 13 399 ridgeSupport224_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
