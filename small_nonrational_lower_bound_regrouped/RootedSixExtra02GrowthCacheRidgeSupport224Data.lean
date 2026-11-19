module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
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
cert_ridgeSupport_code_3 224
cert_ridgeSupport_rest_2 224 000 0
cert_ridgeSupport_rest_2 224 001 416
cert_ridgeSupport_rest_2 224 002 832
cert_ridgeSupport_rest_2 224 003 1248
cert_ridgeSupport_rest_2 224 004 1664
cert_ridgeSupport_rest_2 224 005 2080
cert_ridgeSupport_rest_2 224 006 2496
cert_ridgeSupport_rest_2 224 007 2912
cert_ridgeSupport_rest_2 224 008 3328
cert_ridgeSupport_rest_2 224 009 3744
cert_ridgeSupport_rest_2 224 010 3887
cert_ridgeSupport_suffix_4 224 010
cert_ridgeSupport_suffix_3 224 009 010
cert_ridgeSupport_suffix_3 224 008 009
cert_ridgeSupport_suffix_3 224 007 008
cert_ridgeSupport_suffix_3 224 006 007
cert_ridgeSupport_suffix_3 224 005 006
cert_ridgeSupport_suffix_3 224 004 005
cert_ridgeSupport_suffix_3 224 003 004
cert_ridgeSupport_suffix_3 224 002 003
cert_ridgeSupport_suffix_3 224 001 002
cert_ridgeSupport_suffix_3 224 000 001
cert_ridgeSupport_source_3 224 13 299
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
