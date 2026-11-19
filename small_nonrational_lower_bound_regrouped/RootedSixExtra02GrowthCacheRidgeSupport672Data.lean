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
def ridgeSupport672_000 : List Nat := [51,81,91,98,100,663,664,665,666,673,674,793,794,795,798,799,804,805,810,812,834,836,838,840,842,847,848,850,853,1037,1038,1039]
def ridgeSupport672_001 : List Nat := [1040,1047,1048,1167,1168,1169,1172,1173,1178,1179,1184,1186,1208,1210,1212,1214,1216,1221,1222,1224,1227,1276,1277,1278,1281,1282,1287,1288,1293,1295,1317,1319]
def ridgeSupport672_002 : List Nat := [1321,1323,1325,1330,1331,1333,1336,1363,1365,1367,1369,1370,1372,1374,1375,1379,1381,1386,1387,3740,3745,3754,3756,3822,3823,3832,3833,3838,3839,3842,3844,3848]
def ridgeSupport672_003 : List Nat := [3849,3855,3858,3870,3871,3880,3881,3908,3913,3918,3919,3922,3924,3928,3929,3934,3935,3944,3945,3958,3959,3968,3969,3980,3985,3994,3996,4062,4063,4072,4073,4078]
def ridgeSupport672_004 : List Nat := [4079,4082,4084,4088,4089,4095,4098,4110,4111,4120,4121,4148,4153,4158,4159,4162,4164,4168,4169,4174,4175,4184,4185,4198,4199,4208,4209,4300,4302,4312,4314,4328]
def ridgeSupport672_005 : List Nat := [4329,4340,4341,4442,4447,4454,4459,4474,4475,4486,4487,4508,4513,4522,4524,4590,4591,4600,4601,4606,4607,4610,4612,4616,4617,4623,4626,4638,4639,4648,4649,4676]
def ridgeSupport672_006 : List Nat := [4681,4686,4687,4690,4692,4696,4697,4702,4703,4712,4713,4726,4727,4736,4737,4812,4813,4820,4821,4924,4926,4936,4938,4952,4953,4964,4965,5066,5071,5078,5083,5098]
def ridgeSupport672_007 : List Nat := [5099,5110,5111,5264,5269,5270,5274,5276,5281,5282,5286,5294,5295,5308,5309,5312,5317,5318,5322,5330,5331,5344,5345,5698,5699,5734,5735,5794,5795,6342,6343,6352]
def ridgeSupport672_008 : List Nat := [6353,6357,6358,6359,6360,6365,6366,6390,6391,6400,6401,6405,6406,6407,6408,6413,6414,6446,6447,6449,6451,6483,6484,6485,6486,6510,6511,6520,6521,6525,6526,6527]
def ridgeSupport672_009 : List Nat := [6528,6533,6534,6566,6567,6569,6571,6603,6604,6605,6606]
cert_ridgeSupport_code_3 672
cert_ridgeSupport_rest_2 672 000 0
cert_ridgeSupport_rest_2 672 001 416
cert_ridgeSupport_rest_2 672 002 832
cert_ridgeSupport_rest_2 672 003 1248
cert_ridgeSupport_rest_2 672 004 1664
cert_ridgeSupport_rest_2 672 005 2080
cert_ridgeSupport_rest_2 672 006 2496
cert_ridgeSupport_rest_2 672 007 2912
cert_ridgeSupport_rest_2 672 008 3328
cert_ridgeSupport_rest_2 672 009 3744
cert_ridgeSupport_rest_2 672 010 3887
cert_ridgeSupport_suffix_4 672 010
cert_ridgeSupport_suffix_3 672 009 010
cert_ridgeSupport_suffix_3 672 008 009
cert_ridgeSupport_suffix_3 672 007 008
cert_ridgeSupport_suffix_3 672 006 007
cert_ridgeSupport_suffix_3 672 005 006
cert_ridgeSupport_suffix_3 672 004 005
cert_ridgeSupport_suffix_3 672 003 004
cert_ridgeSupport_suffix_3 672 002 003
cert_ridgeSupport_suffix_3 672 001 002
cert_ridgeSupport_suffix_3 672 000 001
cert_ridgeSupport_source_3 672 13 299
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
