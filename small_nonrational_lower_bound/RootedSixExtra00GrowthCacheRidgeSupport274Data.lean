module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport274_000 : List Nat := [37,47,56,58,60,635,638,639,642,645,659,662,663,666,669,684,685,688,689,694,791,794,795,798,801,815,818,819,822,825,840,841]
def ridgeSupport274_001 : List Nat := [844,845,850,935,936,938,939,942,943,944,946,947,949,954,955,977,979,980,982,983,985,987,988,990,991,994,995,998,1000,1001,1003,1004]
def ridgeSupport274_002 : List Nat := [1006,1008,1009,1011,1012,1015,1016,4170,4171,4176,4177,4180,4181,4182,4183,4184,4185,4190,4191,4194,4195,4200,4201,4204,4205,4206,4207,4208,4209,4214,4215,4228]
def ridgeSupport274_003 : List Nat := [4229,4230,4231,4232,4233,4252,4253,4254,4255,4256,4257,4276,4277,4278,4279,4280,4281,4300,4301,4302,4303,4304,4305,4324,4325,4326,4327,4328,4329,4348,4349,4350]
def ridgeSupport274_004 : List Nat := [4351,4352,4353,4361,4364,4367,4370,4372,4373,4374,4375,4376,4377,4378,4380,4658,4659,4676,4677,4694,4695,4696,4698,4702,4704,4712,4713,4800,4801,4818,4819,4836]
def ridgeSupport274_005 : List Nat := [4837,4841,4844,4847,4850,4854,4855,4872,4873,4890,4891,4908,4909,4913,4916,4919,4922,4926,4927,5186,5187,5204,5205,5222,5223,5224,5226,5230,5232,5240,5241,5328]
def ridgeSupport274_006 : List Nat := [5329,5346,5347,5364,5365,5369,5372,5375,5378,5382,5383,5400,5401,5418,5419,5436,5437,5441,5444,5447,5450,5454,5455,7348,7349,7350,7351,7352,7353,8188,8189,8190]
def ridgeSupport274_007 : List Nat := [8191,8192,8193,8201,8204,8207,8209,8210,8211,8213,8216,8219,8221,8222,8223,8272,8274,8288,8289,8309,8312,8322,8323,8327,8330,8340,8341,8392,8394,8408,8409,8429]
cert_ridgeSupport_7 274 008 8432 8442 8443 8447 8450 8460 8461
cert_ridgeSupport_code_3 274
cert_ridgeSupport_rest_2 274 000 0
cert_ridgeSupport_rest_2 274 001 448
cert_ridgeSupport_rest_2 274 002 896
cert_ridgeSupport_rest_2 274 003 1344
cert_ridgeSupport_rest_2 274 004 1792
cert_ridgeSupport_rest_2 274 005 2240
cert_ridgeSupport_rest_2 274 006 2688
cert_ridgeSupport_rest_2 274 007 3136
cert_ridgeSupport_rest_2 274 008 3584
cert_ridgeSupport_rest_2 274 009 3682
cert_ridgeSupport_suffix_4 274 009
cert_ridgeSupport_suffix_3 274 008 009
cert_ridgeSupport_suffix_3 274 007 008
cert_ridgeSupport_suffix_3 274 006 007
cert_ridgeSupport_suffix_3 274 005 006
cert_ridgeSupport_suffix_3 274 004 005
cert_ridgeSupport_suffix_3 274 003 004
cert_ridgeSupport_suffix_3 274 002 003
cert_ridgeSupport_suffix_3 274 001 002
cert_ridgeSupport_suffix_3 274 000 001
cert_ridgeSupport_source_3 274 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
