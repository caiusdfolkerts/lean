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
def ridgeSupport168_000 : List Nat := [38,68,77,80,81,616,617,619,624,626,651,654,656,659,661,663,666,668,671,673,989,992,993,996,999,1026,1027,1030,1031,1036,1038,1039]
def ridgeSupport168_001 : List Nat := [1042,1043,1048,1145,1147,1148,1150,1151,1153,1155,1156,1158,1159,1162,1163,1166,1168,1169,1171,1172,1174,1176,1177,1179,1180,1183,1184,1209,1210,1212,1213,1214]
def ridgeSupport168_002 : List Nat := [1215,1217,1218,1220,1221,1223,1224,3980,3981,3986,3987,3988,3989,3990,3991,3994,3995,4000,4001,4004,4005,4010,4011,4012,4013,4014,4015,4018,4019,4024,4025,4034]
def ridgeSupport168_003 : List Nat := [4035,4036,4037,4038,4039,4058,4059,4060,4061,4062,4063,4082,4083,4084,4085,4086,4087,4106,4107,4108,4109,4110,4111,4130,4131,4132,4133,4134,4135,4154,4155,4156]
def ridgeSupport168_004 : List Nat := [4157,4158,4159,4175,4177,4178,4179,4180,4181,4182,4183,4185,4188,4191,4194,4240,4241,4252,4253,4257,4260,4263,4266,4276,4277,4288,4289,4312,4313,4324,4325,4329]
def ridgeSupport168_005 : List Nat := [4332,4335,4338,4348,4349,4360,4361,4454,4455,4466,4467,4475,4477,4481,4483,4490,4491,4502,4503,4852,4853,4870,4871,4888,4889,4893,4896,4899,4902,4906,4907,4924]
def ridgeSupport168_006 : List Nat := [4925,4942,4943,4960,4961,4965,4968,4971,4974,4978,4979,5066,5067,5084,5085,5102,5103,5111,5113,5117,5119,5120,5121,5276,5277,5282,5283,5284,5285,5289,5292,5295]
def ridgeSupport168_007 : List Nat := [5298,5309,5311,5324,5329,5330,5335,5344,5346,5714,5715,5716,5717,5718,5719,6386,6387,6388,6389,6390,6391,6407,6409,6410,6411,6412,6413,6419,6421,6422,6423,6424]
def ridgeSupport168_008 : List Nat := [6425,6430,6431,6436,6437,6448,6449,6454,6455,6482,6483,6488,6489,6549,6552,6562,6563,6567,6570,6580,6581,6605,6607,6614,6615]
cert_ridgeSupport_code_3 168
cert_ridgeSupport_rest_2 168 000 0
cert_ridgeSupport_rest_2 168 001 416
cert_ridgeSupport_rest_2 168 002 832
cert_ridgeSupport_rest_2 168 003 1248
cert_ridgeSupport_rest_2 168 004 1664
cert_ridgeSupport_rest_2 168 005 2080
cert_ridgeSupport_rest_2 168 006 2496
cert_ridgeSupport_rest_2 168 007 2912
cert_ridgeSupport_rest_2 168 008 3328
cert_ridgeSupport_rest_2 168 009 3653
cert_ridgeSupport_suffix_4 168 009
cert_ridgeSupport_suffix_3 168 008 009
cert_ridgeSupport_suffix_3 168 007 008
cert_ridgeSupport_suffix_3 168 006 007
cert_ridgeSupport_suffix_3 168 005 006
cert_ridgeSupport_suffix_3 168 004 005
cert_ridgeSupport_suffix_3 168 003 004
cert_ridgeSupport_suffix_3 168 002 003
cert_ridgeSupport_suffix_3 168 001 002
cert_ridgeSupport_suffix_3 168 000 001
cert_ridgeSupport_source_3 168 13 281
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
