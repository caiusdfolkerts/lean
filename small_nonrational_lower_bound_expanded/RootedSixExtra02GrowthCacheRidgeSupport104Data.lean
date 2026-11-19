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
def ridgeSupport104_000 : List Nat := [37,67,77,78,79,615,618,620,623,625,627,630,632,635,637,639,642,644,647,649,990,991,994,995,1000,1002,1003,1006,1007,1012,1014,1015]
def ridgeSupport104_001 : List Nat := [1018,1019,1024,1146,1147,1149,1150,1151,1152,1154,1155,1157,1158,1160,1161,1167,1168,1170,1171,1172,1173,1175,1176,1178,1179,1181,1182,1188,1189,1191,1192,1193]
def ridgeSupport104_002 : List Nat := [1194,1196,1197,1199,1200,1202,1203,3980,3981,3982,3983,3984,3985,3986,3987,3992,3993,3998,3999,4004,4005,4006,4007,4008,4009,4010,4011,4016,4017,4022,4023,4028]
def ridgeSupport104_003 : List Nat := [4029,4030,4031,4032,4033,4052,4053,4054,4055,4056,4057,4076,4077,4078,4079,4080,4081,4100,4101,4102,4103,4104,4105,4124,4125,4126,4127,4128,4129,4148,4149,4150]
def ridgeSupport104_004 : List Nat := [4151,4152,4153,4172,4173,4174,4175,4176,4177,4181,4183,4187,4189,4193,4195,4238,4239,4250,4251,4259,4261,4265,4267,4274,4275,4286,4287,4310,4311,4322,4323,4331]
def ridgeSupport104_005 : List Nat := [4333,4337,4339,4346,4347,4358,4359,4382,4383,4394,4395,4403,4405,4409,4411,4418,4419,4430,4431,4850,4851,4868,4869,4886,4887,4895,4897,4901,4903,4904,4905,4922]
def ridgeSupport104_006 : List Nat := [4923,4940,4941,4958,4959,4967,4969,4973,4975,4976,4977,4994,4995,5012,5013,5030,5031,5039,5041,5045,5047,5048,5049,5276,5277,5278,5279,5280,5281,5291,5293,5297]
def ridgeSupport104_007 : List Nat := [5299,5303,5305,5326,5328,5332,5334,5338,5340,5708,5709,5710,5711,5712,5713,6380,6381,6382,6383,6384,6385,6404,6405,6406,6407,6408,6409,6416,6417,6418,6419,6420]
def ridgeSupport104_008 : List Nat := [6421,6428,6429,6434,6435,6446,6447,6452,6453,6464,6465,6470,6471,6551,6553,6560,6561,6569,6571,6578,6579,6587,6589,6596,6597]
cert_ridgeSupport_code_3 104
cert_ridgeSupport_rest_2 104 000 0
cert_ridgeSupport_rest_2 104 001 416
cert_ridgeSupport_rest_2 104 002 832
cert_ridgeSupport_rest_2 104 003 1248
cert_ridgeSupport_rest_2 104 004 1664
cert_ridgeSupport_rest_2 104 005 2080
cert_ridgeSupport_rest_2 104 006 2496
cert_ridgeSupport_rest_2 104 007 2912
cert_ridgeSupport_rest_2 104 008 3328
cert_ridgeSupport_rest_2 104 009 3653
cert_ridgeSupport_suffix_4 104 009
cert_ridgeSupport_suffix_3 104 008 009
cert_ridgeSupport_suffix_3 104 007 008
cert_ridgeSupport_suffix_3 104 006 007
cert_ridgeSupport_suffix_3 104 005 006
cert_ridgeSupport_suffix_3 104 004 005
cert_ridgeSupport_suffix_3 104 003 004
cert_ridgeSupport_suffix_3 104 002 003
cert_ridgeSupport_suffix_3 104 001 002
cert_ridgeSupport_suffix_3 104 000 001
cert_ridgeSupport_source_3 104 13 281
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
