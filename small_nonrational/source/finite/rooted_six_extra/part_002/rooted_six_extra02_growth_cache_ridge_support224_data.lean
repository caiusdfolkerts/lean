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
def ridgeSupport224_000 : List Nat := [47,77,87,97,98,615,616,617,618,625,626,771,772,776,778,779,783,785,786,788,792,793,797,799,800,804,806,807,809,989,990,991]
def ridgeSupport224_001 : List Nat := [992,999,1000,1145,1146,1150,1152,1153,1157,1159,1160,1162,1166,1167,1171,1173,1174,1178,1180,1181,1183,1254,1255,1259,1261,1262,1266,1268,1269,1271,1275,1276]
def ridgeSupport224_002 : List Nat := [1280,1282,1283,1287,1289,1290,1292,1365,1366,1368,1369,1370,1371,1373,1374,1376,1377,1379,1380,3753,3755,3759,3761,3812,3813,3818,3819,3839,3841,3845,3847,3852]
def ridgeSupport224_003 : List Nat := [3853,3858,3859,3860,3861,3866,3867,3908,3909,3914,3915,3921,3923,3927,3929,3948,3949,3954,3955,3972,3973,3978,3979,3993,3995,3999,4001,4052,4053,4058,4059,4079]
def ridgeSupport224_004 : List Nat := [4081,4085,4087,4092,4093,4098,4099,4100,4101,4106,4107,4148,4149,4154,4155,4161,4163,4167,4169,4188,4189,4194,4195,4212,4213,4218,4219,4227,4229,4239,4241,4260]
def ridgeSupport224_005 : List Nat := [4261,4272,4273,4299,4301,4311,4313,4332,4333,4344,4345,4521,4523,4527,4529,4580,4581,4586,4587,4607,4609,4613,4615,4620,4621,4626,4627,4628,4629,4634,4635,4676]
def ridgeSupport224_006 : List Nat := [4677,4682,4683,4689,4691,4695,4697,4716,4717,4722,4723,4740,4741,4746,4747,4748,4749,4756,4757,4851,4853,4863,4865,4884,4885,4896,4897,4923,4925,4935,4937,4956]
def ridgeSupport224_007 : List Nat := [4957,4968,4969,5267,5269,5271,5273,5279,5281,5283,5285,5292,5293,5298,5299,5315,5317,5319,5321,5328,5329,5334,5335,5706,5707,5742,5743,5802,5803,6332,6333,6338]
def ridgeSupport224_008 : List Nat := [6339,6356,6357,6362,6363,6366,6367,6380,6381,6386,6387,6404,6405,6410,6411,6414,6415,6428,6430,6432,6433,6446,6448,6450,6451,6500,6501,6506,6507,6524,6525,6530]
def ridgeSupport224_009 : List Nat := [6531,6534,6535,6548,6550,6552,6553,6566,6568,6570,6571]
def ridgeSupport224_code : Nat := 0x66af3559a8cd36667331996cca661f30d983cc165f72f996bcb565972c9933c9964c325d921c90647b23990fc87642f215905c8263cf1e58edc76637f1bd8dbc6d63571a98c3c6162f71796abb5559becdd64bb25535e9ad4d1a68532698f4c5a61d2ce9654ada5652969474a1a4fd26692f495a49cda66d135d9ae4d2668f33d99dcc8664131598a4c065ff2f5979ca5652928d9464a2e51528594249ce4e526d93649664af253928c92e495245922486e43521590a484e42520d906481e40b2018ffc7ae3d51e58f246c635f1ab8d4c3e61f10ed87643661af0cd865c2c61610a5852424611f085841c1ee0f507583a418e0c505d82e412608f043820c0ee07503581a402e015005802400e004ffd7fe3fddfeaff17f7bf6dfb4fd57ea3e85f3ef9b7ccbe2df14f857c23dcdee4f6d7b63d65eaef537a8bd2de94f457a23c6de34f1578a3c4de24f0d7863c1de0af0177fbbaddd4ee57723ac5d5eeab7549590ac65612b01578aba55b2ad1564ab05562aa9430a14509283940ca0450027e13ec9ee4f527a13c89dc4ed275939c9cc49f24e927093449624a924c91e48e245122090e48524092008fc47a23c8fa07ce3e01ef8f787ba3291938c9864832018f8c7463231818a0c4862230f1858c2861030418189c84e226a13489a04ce062030815c09a02f
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
def ridgeSupport224_rest_010 : Nat := PackedRawNatGrowth.drop 3887 ridgeSupport224_code
def ridgeSupport224_suffix_010 : List Nat := []
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
    (PackedRawNatGrowth.readList 13 299 ridgeSupport224_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
