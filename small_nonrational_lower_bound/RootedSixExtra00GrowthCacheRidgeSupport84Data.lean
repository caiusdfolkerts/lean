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
def ridgeSupport84_000 : List Nat := [35,75,79,80,81,623,626,628,631,633,635,638,640,643,645,647,650,652,655,657,1201,1203,1204,1207,1209,1213,1215,1216,1219,1221,1225,1227]
def ridgeSupport84_001 : List Nat := [1228,1231,1233,1273,1274,1276,1277,1278,1279,1281,1282,1284,1285,1287,1288,1294,1295,1297,1298,1299,1300,1302,1303,1305,1306,1308,1309,1315,1316,1318,1319,1320]
def ridgeSupport84_002 : List Nat := [1321,1323,1324,1326,1327,1329,1330,4408,4409,4410,4411,4412,4413,4414,4415,4420,4421,4426,4427,4432,4433,4434,4435,4436,4437,4438,4439,4444,4445,4450,4451,4456]
def ridgeSupport84_003 : List Nat := [4457,4458,4459,4460,4461,4480,4481,4482,4483,4484,4485,4504,4505,4506,4507,4508,4509,4528,4529,4530,4531,4532,4533,4552,4553,4554,4555,4556,4557,4576,4577,4578]
def ridgeSupport84_004 : List Nat := [4579,4580,4581,4600,4601,4602,4603,4604,4605,4609,4611,4615,4617,4621,4623,4666,4667,4678,4679,4687,4689,4693,4695,4702,4703,4714,4715,4738,4739,4750,4751,4759]
def ridgeSupport84_005 : List Nat := [4761,4765,4767,4774,4775,4786,4787,4810,4811,4822,4823,4831,4833,4837,4839,4846,4847,4858,4859,6472,6473,6484,6485,6508,6509,6520,6521,6535,6537,6541,6543,6544]
def ridgeSupport84_006 : List Nat := [6545,6556,6557,6580,6581,6592,6593,6607,6609,6613,6615,6616,6617,6628,6629,6652,6653,6664,6665,6679,6681,6685,6687,7372,7373,7374,7375,7376,7377,8224,8225,8226]
def ridgeSupport84_007 : List Nat := [8227,8228,8229,8248,8249,8250,8251,8252,8253,8260,8261,8262,8263,8264,8265,8272,8273,8278,8279,8290,8291,8296,8297,8308,8309,8314,8315,8689,8691,8695,8697,8707]
cert_ridgeSupport_7 84 008 8709 8713 8715 8725 8727 8731 8733
cert_ridgeSupport_code_3 84
cert_ridgeSupport_rest_2 84 000 0
cert_ridgeSupport_rest_2 84 001 448
cert_ridgeSupport_rest_2 84 002 896
cert_ridgeSupport_rest_2 84 003 1344
cert_ridgeSupport_rest_2 84 004 1792
cert_ridgeSupport_rest_2 84 005 2240
cert_ridgeSupport_rest_2 84 006 2688
cert_ridgeSupport_rest_2 84 007 3136
cert_ridgeSupport_rest_2 84 008 3584
cert_ridgeSupport_rest_2 84 009 3682
cert_ridgeSupport_suffix_4 84 009
cert_ridgeSupport_suffix_3 84 008 009
cert_ridgeSupport_suffix_3 84 007 008
cert_ridgeSupport_suffix_3 84 006 007
cert_ridgeSupport_suffix_3 84 005 006
cert_ridgeSupport_suffix_3 84 004 005
cert_ridgeSupport_suffix_3 84 003 004
cert_ridgeSupport_suffix_3 84 002 003
cert_ridgeSupport_suffix_3 84 001 002
cert_ridgeSupport_suffix_3 84 000 001
cert_ridgeSupport_source_3 84 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
