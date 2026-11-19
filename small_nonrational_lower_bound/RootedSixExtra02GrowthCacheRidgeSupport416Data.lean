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
def ridgeSupport416_000 : List Nat := [50,80,90,97,100,651,652,653,654,661,662,772,773,774,777,778,783,784,789,791,834,835,839,841,842,846,848,849,851,1025,1026,1027]
def ridgeSupport416_001 : List Nat := [1028,1035,1036,1146,1147,1148,1151,1152,1157,1158,1163,1165,1208,1209,1213,1215,1216,1220,1222,1223,1225,1255,1256,1257,1260,1261,1266,1267,1272,1274,1317,1318]
def ridgeSupport416_002 : List Nat := [1322,1324,1325,1329,1331,1332,1334,1363,1366,1367,1368,1371,1372,1373,1375,1380,1381,1383,1384,3741,3743,3760,3762,3820,3821,3826,3827,3840,3841,3843,3846,3849]
def ridgeSupport416_003 : List Nat := [3852,3854,3855,3868,3869,3874,3875,3909,3911,3916,3917,3922,3923,3928,3930,3936,3937,3950,3951,3960,3961,3974,3975,3981,3983,4000,4002,4060,4061,4066,4067,4080]
def ridgeSupport416_004 : List Nat := [4081,4083,4086,4089,4092,4094,4095,4108,4109,4114,4115,4149,4151,4156,4157,4162,4163,4168,4170,4176,4177,4190,4191,4200,4201,4214,4215,4228,4230,4240,4242,4256]
def ridgeSupport416_005 : List Nat := [4257,4268,4269,4443,4445,4455,4457,4476,4477,4488,4489,4509,4511,4528,4530,4588,4589,4594,4595,4608,4609,4611,4614,4617,4620,4622,4623,4636,4637,4642,4643,4677]
def ridgeSupport416_006 : List Nat := [4679,4684,4685,4690,4691,4696,4698,4704,4705,4718,4719,4728,4729,4742,4743,4796,4797,4804,4805,4852,4854,4864,4866,4880,4881,4892,4893,5067,5069,5079,5081,5100]
def ridgeSupport416_007 : List Nat := [5101,5112,5113,5265,5267,5272,5274,5277,5279,5284,5286,5288,5289,5310,5311,5313,5315,5320,5322,5324,5325,5346,5347,5700,5701,5736,5737,5796,5797,6340,6341,6346]
def ridgeSupport416_008 : List Nat := [6347,6356,6358,6360,6361,6364,6367,6388,6389,6394,6395,6404,6406,6408,6409,6412,6415,6428,6429,6431,6433,6482,6484,6486,6487,6508,6509,6514,6515,6524,6526,6528]
def ridgeSupport416_009 : List Nat := [6529,6532,6535,6548,6549,6551,6553,6602,6604,6606,6607]
cert_ridgeSupport_code_3 416
cert_ridgeSupport_rest_2 416 000 0
cert_ridgeSupport_rest_2 416 001 416
cert_ridgeSupport_rest_2 416 002 832
cert_ridgeSupport_rest_2 416 003 1248
cert_ridgeSupport_rest_2 416 004 1664
cert_ridgeSupport_rest_2 416 005 2080
cert_ridgeSupport_rest_2 416 006 2496
cert_ridgeSupport_rest_2 416 007 2912
cert_ridgeSupport_rest_2 416 008 3328
cert_ridgeSupport_rest_2 416 009 3744
cert_ridgeSupport_rest_2 416 010 3887
cert_ridgeSupport_suffix_4 416 010
cert_ridgeSupport_suffix_3 416 009 010
cert_ridgeSupport_suffix_3 416 008 009
cert_ridgeSupport_suffix_3 416 007 008
cert_ridgeSupport_suffix_3 416 006 007
cert_ridgeSupport_suffix_3 416 005 006
cert_ridgeSupport_suffix_3 416 004 005
cert_ridgeSupport_suffix_3 416 003 004
cert_ridgeSupport_suffix_3 416 002 003
cert_ridgeSupport_suffix_3 416 001 002
cert_ridgeSupport_suffix_3 416 000 001
cert_ridgeSupport_source_3 416 13 299
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
