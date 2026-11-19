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
def ridgeSupport296_000 : List Nat := [39,69,78,80,82,628,629,631,636,638,652,653,655,660,662,675,678,680,683,685,1001,1004,1005,1008,1011,1025,1028,1029,1032,1035,1050,1051]
def ridgeSupport296_001 : List Nat := [1054,1055,1060,1145,1146,1148,1149,1152,1153,1154,1156,1157,1159,1164,1165,1187,1189,1190,1192,1193,1195,1197,1198,1200,1201,1204,1205,1208,1210,1211,1213,1214]
def ridgeSupport296_002 : List Nat := [1216,1218,1219,1221,1222,1225,1226,3982,3983,3988,3989,3992,3993,3994,3995,3996,3997,4002,4003,4006,4007,4012,4013,4016,4017,4018,4019,4020,4021,4026,4027,4040]
def ridgeSupport296_003 : List Nat := [4041,4042,4043,4044,4045,4064,4065,4066,4067,4068,4069,4088,4089,4090,4091,4092,4093,4112,4113,4114,4115,4116,4117,4136,4137,4138,4139,4140,4141,4160,4161,4162]
def ridgeSupport296_004 : List Nat := [4163,4164,4165,4173,4176,4179,4182,4184,4185,4186,4187,4188,4189,4190,4192,4242,4243,4254,4255,4256,4258,4262,4264,4278,4279,4290,4291,4384,4385,4396,4397,4401]
def ridgeSupport296_005 : List Nat := [4404,4407,4410,4420,4421,4432,4433,4456,4457,4468,4469,4473,4476,4479,4482,4492,4493,4504,4505,4854,4855,4872,4873,4890,4891,4892,4894,4898,4900,4908,4909,4996]
def ridgeSupport296_006 : List Nat := [4997,5014,5015,5032,5033,5037,5040,5043,5046,5050,5051,5068,5069,5086,5087,5104,5105,5109,5112,5115,5118,5122,5123,5278,5279,5282,5283,5286,5287,5288,5290,5301]
def ridgeSupport296_007 : List Nat := [5304,5307,5310,5325,5327,5336,5341,5342,5347,5720,5721,5722,5723,5724,5725,6392,6393,6394,6395,6396,6397,6405,6408,6411,6413,6414,6415,6417,6420,6423,6425,6426]
def ridgeSupport296_008 : List Nat := [6427,6432,6433,6438,6439,6466,6467,6472,6473,6484,6485,6490,6491,6548,6550,6564,6565,6585,6588,6598,6599,6603,6606,6616,6617]
cert_ridgeSupport_code_3 296
cert_ridgeSupport_rest_2 296 000 0
cert_ridgeSupport_rest_2 296 001 416
cert_ridgeSupport_rest_2 296 002 832
cert_ridgeSupport_rest_2 296 003 1248
cert_ridgeSupport_rest_2 296 004 1664
cert_ridgeSupport_rest_2 296 005 2080
cert_ridgeSupport_rest_2 296 006 2496
cert_ridgeSupport_rest_2 296 007 2912
cert_ridgeSupport_rest_2 296 008 3328
cert_ridgeSupport_rest_2 296 009 3653
cert_ridgeSupport_suffix_4 296 009
cert_ridgeSupport_suffix_3 296 008 009
cert_ridgeSupport_suffix_3 296 007 008
cert_ridgeSupport_suffix_3 296 006 007
cert_ridgeSupport_suffix_3 296 005 006
cert_ridgeSupport_suffix_3 296 004 005
cert_ridgeSupport_suffix_3 296 003 004
cert_ridgeSupport_suffix_3 296 002 003
cert_ridgeSupport_suffix_3 296 001 002
cert_ridgeSupport_suffix_3 296 000 001
cert_ridgeSupport_source_3 296 13 281
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
