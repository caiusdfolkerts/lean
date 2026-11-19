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
def ridgeSupport352_000 : List Nat := [48,78,88,97,99,627,628,629,630,637,638,771,773,775,777,779,784,785,787,790,813,814,818,820,821,825,827,828,830,1001,1002,1003]
def ridgeSupport352_001 : List Nat := [1004,1011,1012,1145,1147,1149,1151,1153,1158,1159,1161,1164,1187,1188,1192,1194,1195,1199,1201,1202,1204,1254,1256,1258,1260,1262,1267,1268,1270,1273,1296,1297]
def ridgeSupport352_002 : List Nat := [1301,1303,1304,1308,1310,1311,1313,1364,1366,1367,1369,1370,1372,1374,1375,1377,1378,1382,1383,3747,3749,3758,3763,3814,3815,3824,3825,3837,3840,3846,3847,3851]
def ridgeSupport352_003 : List Nat := [3853,3856,3857,3862,3863,3872,3873,3910,3911,3915,3917,3920,3921,3926,3931,3942,3943,3952,3953,3966,3967,3976,3977,3987,3989,3998,4003,4054,4055,4064,4065,4077]
def ridgeSupport352_004 : List Nat := [4080,4086,4087,4091,4093,4096,4097,4102,4103,4112,4113,4150,4151,4155,4157,4160,4161,4166,4171,4182,4183,4192,4193,4206,4207,4216,4217,4226,4231,4238,4243,4258]
def ridgeSupport352_005 : List Nat := [4259,4270,4271,4371,4373,4383,4385,4404,4405,4416,4417,4515,4517,4526,4531,4582,4583,4592,4593,4605,4608,4614,4615,4619,4621,4624,4625,4630,4631,4640,4641,4678]
def ridgeSupport352_006 : List Nat := [4679,4683,4685,4688,4689,4694,4699,4710,4711,4720,4721,4734,4735,4744,4745,4764,4765,4772,4773,4850,4855,4862,4867,4882,4883,4894,4895,4995,4997,5007,5009,5028]
def ridgeSupport352_007 : List Nat := [5029,5040,5041,5265,5268,5271,5275,5277,5280,5283,5287,5290,5291,5304,5305,5313,5316,5319,5323,5326,5327,5340,5341,5704,5705,5740,5741,5800,5801,6334,6335,6344]
def ridgeSupport352_008 : List Nat := [6345,6358,6359,6362,6364,6365,6366,6382,6383,6392,6393,6406,6407,6410,6412,6413,6414,6429,6430,6431,6432,6464,6466,6468,6469,6502,6503,6512,6513,6526,6527,6530]
def ridgeSupport352_009 : List Nat := [6532,6533,6534,6549,6550,6551,6552,6584,6586,6588,6589]
cert_ridgeSupport_code_3 352
cert_ridgeSupport_rest_2 352 000 0
cert_ridgeSupport_rest_2 352 001 416
cert_ridgeSupport_rest_2 352 002 832
cert_ridgeSupport_rest_2 352 003 1248
cert_ridgeSupport_rest_2 352 004 1664
cert_ridgeSupport_rest_2 352 005 2080
cert_ridgeSupport_rest_2 352 006 2496
cert_ridgeSupport_rest_2 352 007 2912
cert_ridgeSupport_rest_2 352 008 3328
cert_ridgeSupport_rest_2 352 009 3744
cert_ridgeSupport_rest_2 352 010 3887
cert_ridgeSupport_suffix_4 352 010
cert_ridgeSupport_suffix_3 352 009 010
cert_ridgeSupport_suffix_3 352 008 009
cert_ridgeSupport_suffix_3 352 007 008
cert_ridgeSupport_suffix_3 352 006 007
cert_ridgeSupport_suffix_3 352 005 006
cert_ridgeSupport_suffix_3 352 004 005
cert_ridgeSupport_suffix_3 352 003 004
cert_ridgeSupport_suffix_3 352 002 003
cert_ridgeSupport_suffix_3 352 001 002
cert_ridgeSupport_suffix_3 352 000 001
cert_ridgeSupport_source_3 352 13 299
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
