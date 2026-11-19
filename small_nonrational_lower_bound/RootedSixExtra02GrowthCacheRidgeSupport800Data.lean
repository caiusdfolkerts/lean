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
def ridgeSupport800_000 : List Nat := [52,82,92,99,100,675,676,677,678,685,686,814,815,816,819,820,825,826,831,833,835,836,837,840,841,846,847,852,854,1049,1050,1051]
def ridgeSupport800_001 : List Nat := [1052,1059,1060,1188,1189,1190,1193,1194,1199,1200,1205,1207,1209,1210,1211,1214,1215,1220,1221,1226,1228,1297,1298,1299,1302,1303,1308,1309,1314,1316,1318,1319]
def ridgeSupport800_002 : List Nat := [1320,1323,1324,1329,1330,1335,1337,1363,1364,1368,1369,1370,1371,1373,1374,1382,1384,1385,1387,3742,3744,3748,3750,3828,3829,3834,3835,3836,3837,3842,3843,3848]
def ridgeSupport800_003 : List Nat := [3850,3854,3856,3876,3877,3882,3883,3910,3912,3916,3918,3924,3925,3930,3931,3932,3933,3938,3939,3956,3957,3962,3963,3982,3984,3988,3990,4068,4069,4074,4075,4076]
def ridgeSupport800_004 : List Nat := [4077,4082,4083,4088,4090,4094,4096,4116,4117,4122,4123,4150,4152,4156,4158,4164,4165,4170,4171,4172,4173,4178,4179,4196,4197,4202,4203,4372,4374,4384,4386,4400]
def ridgeSupport800_005 : List Nat := [4401,4412,4413,4444,4446,4456,4458,4472,4473,4484,4485,4510,4512,4516,4518,4596,4597,4602,4603,4604,4605,4610,4611,4616,4618,4622,4624,4644,4645,4650,4651,4678]
def ridgeSupport800_006 : List Nat := [4680,4684,4686,4692,4693,4698,4699,4700,4701,4706,4707,4724,4725,4730,4731,4828,4829,4836,4837,4996,4998,5008,5010,5024,5025,5036,5037,5068,5070,5080,5082,5096]
def ridgeSupport800_007 : List Nat := [5097,5108,5109,5266,5268,5270,5272,5278,5280,5282,5284,5300,5301,5306,5307,5314,5316,5318,5320,5336,5337,5342,5343,5696,5697,5732,5733,5792,5793,6348,6349,6354]
def ridgeSupport800_008 : List Nat := [6355,6356,6357,6359,6361,6362,6363,6396,6397,6402,6403,6404,6405,6407,6409,6410,6411,6464,6465,6467,6469,6482,6483,6485,6487,6516,6517,6522,6523,6524,6525,6527]
def ridgeSupport800_009 : List Nat := [6529,6530,6531,6584,6585,6587,6589,6602,6603,6605,6607]
cert_ridgeSupport_code_3 800
cert_ridgeSupport_rest_2 800 000 0
cert_ridgeSupport_rest_2 800 001 416
cert_ridgeSupport_rest_2 800 002 832
cert_ridgeSupport_rest_2 800 003 1248
cert_ridgeSupport_rest_2 800 004 1664
cert_ridgeSupport_rest_2 800 005 2080
cert_ridgeSupport_rest_2 800 006 2496
cert_ridgeSupport_rest_2 800 007 2912
cert_ridgeSupport_rest_2 800 008 3328
cert_ridgeSupport_rest_2 800 009 3744
cert_ridgeSupport_rest_2 800 010 3887
cert_ridgeSupport_suffix_4 800 010
cert_ridgeSupport_suffix_3 800 009 010
cert_ridgeSupport_suffix_3 800 008 009
cert_ridgeSupport_suffix_3 800 007 008
cert_ridgeSupport_suffix_3 800 006 007
cert_ridgeSupport_suffix_3 800 005 006
cert_ridgeSupport_suffix_3 800 004 005
cert_ridgeSupport_suffix_3 800 003 004
cert_ridgeSupport_suffix_3 800 002 003
cert_ridgeSupport_suffix_3 800 001 002
cert_ridgeSupport_suffix_3 800 000 001
cert_ridgeSupport_source_3 800 13 299
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
