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
def ridgeSupport608_000 : List Nat := [49,79,89,98,99,639,640,641,642,649,650,792,794,796,798,800,805,806,808,811,813,815,817,819,821,826,827,829,832,1013,1014,1015]
def ridgeSupport608_001 : List Nat := [1016,1023,1024,1166,1168,1170,1172,1174,1179,1180,1182,1185,1187,1189,1191,1193,1195,1200,1201,1203,1206,1275,1277,1279,1281,1283,1288,1289,1291,1294,1296,1298]
def ridgeSupport608_002 : List Nat := [1300,1302,1304,1309,1310,1312,1315,1364,1365,1367,1368,1371,1372,1373,1375,1376,1378,1385,1386,3746,3751,3752,3757,3816,3817,3830,3831,3836,3838,3844,3845,3850]
def ridgeSupport608_003 : List Nat := [3851,3857,3859,3864,3865,3878,3879,3912,3913,3914,3919,3920,3925,3926,3927,3940,3941,3946,3947,3964,3965,3970,3971,3986,3991,3992,3997,4056,4057,4070,4071,4076]
def ridgeSupport608_004 : List Nat := [4078,4084,4085,4090,4091,4097,4099,4104,4105,4118,4119,4152,4153,4154,4159,4160,4165,4166,4167,4180,4181,4186,4187,4204,4205,4210,4211,4298,4303,4310,4315,4330]
def ridgeSupport608_005 : List Nat := [4331,4342,4343,4370,4375,4382,4387,4402,4403,4414,4415,4514,4519,4520,4525,4584,4585,4598,4599,4604,4606,4612,4613,4618,4619,4625,4627,4632,4633,4646,4647,4680]
def ridgeSupport608_006 : List Nat := [4681,4682,4687,4688,4693,4694,4695,4708,4709,4714,4715,4732,4733,4738,4739,4780,4781,4788,4789,4922,4927,4934,4939,4954,4955,4966,4967,4994,4999,5006,5011,5026]
def ridgeSupport608_007 : List Nat := [5027,5038,5039,5264,5266,5273,5275,5276,5278,5285,5287,5296,5297,5302,5303,5312,5314,5321,5323,5332,5333,5338,5339,5702,5703,5738,5739,5798,5799,6336,6337,6350]
def ridgeSupport608_008 : List Nat := [6351,6360,6361,6363,6364,6365,6367,6384,6385,6398,6399,6408,6409,6411,6412,6413,6415,6447,6448,6449,6450,6465,6466,6467,6468,6504,6505,6518,6519,6528,6529,6531]
def ridgeSupport608_009 : List Nat := [6532,6533,6535,6567,6568,6569,6570,6585,6586,6587,6588]
cert_ridgeSupport_code_3 608
cert_ridgeSupport_rest_2 608 000 0
cert_ridgeSupport_rest_2 608 001 416
cert_ridgeSupport_rest_2 608 002 832
cert_ridgeSupport_rest_2 608 003 1248
cert_ridgeSupport_rest_2 608 004 1664
cert_ridgeSupport_rest_2 608 005 2080
cert_ridgeSupport_rest_2 608 006 2496
cert_ridgeSupport_rest_2 608 007 2912
cert_ridgeSupport_rest_2 608 008 3328
cert_ridgeSupport_rest_2 608 009 3744
cert_ridgeSupport_rest_2 608 010 3887
cert_ridgeSupport_suffix_4 608 010
cert_ridgeSupport_suffix_3 608 009 010
cert_ridgeSupport_suffix_3 608 008 009
cert_ridgeSupport_suffix_3 608 007 008
cert_ridgeSupport_suffix_3 608 006 007
cert_ridgeSupport_suffix_3 608 005 006
cert_ridgeSupport_suffix_3 608 004 005
cert_ridgeSupport_suffix_3 608 003 004
cert_ridgeSupport_suffix_3 608 002 003
cert_ridgeSupport_suffix_3 608 001 002
cert_ridgeSupport_suffix_3 608 000 001
cert_ridgeSupport_source_3 608 13 299
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
