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
def ridgeSupport592_000 : List Nat := [59,73,89,94,95,901,903,905,907,909,914,915,917,920,922,924,926,928,930,935,936,938,941,1013,1014,1017,1018,1021,1022,1082,1084,1086]
def ridgeSupport592_001 : List Nat := [1088,1090,1095,1096,1098,1101,1103,1105,1107,1109,1111,1116,1117,1119,1122,1276,1278,1280,1281,1283,1285,1286,1290,1295,1297,1299,1301,1302,1304,1306,1307,1311]
def ridgeSupport592_002 : List Nat := [1316,1339,1340,1342,1343,1346,1347,1348,1350,1351,1353,1360,1361,3170,3175,3176,3181,3240,3241,3254,3255,3260,3262,3268,3269,3274,3275,3281,3283,3288,3289,3302]
def ridgeSupport592_003 : List Nat := [3303,3336,3337,3338,3343,3344,3349,3350,3351,3364,3365,3370,3371,3388,3389,3394,3395,3410,3415,3416,3421,3480,3481,3494,3495,3500,3502,3508,3509,3514,3515,3521]
def ridgeSupport592_004 : List Nat := [3523,3528,3529,3542,3543,3576,3577,3578,3583,3584,3589,3590,3591,3604,3605,3610,3611,3628,3629,3634,3635,3680,3681,3684,3685,4538,4543,4544,4549,4560,4561,4574]
def ridgeSupport592_005 : List Nat := [4575,4608,4609,4622,4623,4628,4630,4636,4637,4642,4643,4649,4651,4656,4657,4658,4663,4664,4669,4670,4671,4704,4705,4718,4719,4728,4729,4742,4743,4784,4785,4792]
def ridgeSupport592_006 : List Nat := [4793,4916,4921,4946,4951,4960,4961,4978,4979,4988,4993,5018,5023,5032,5033,5050,5051,5240,5242,5249,5251,5252,5254,5261,5263,5313,5315,5320,5322,5330,5335,5336]
def ridgeSupport592_007 : List Nat := [5341,5606,5607,5642,5643,5796,5797,6240,6241,6254,6255,6264,6265,6267,6268,6269,6271,6288,6289,6302,6303,6312,6313,6315,6316,6317,6319,6500,6502,6521,6523,6540]
def ridgeSupport592_008 : List Nat := [6541,6543,6544,6545,6547,6573,6574,6575,6576,6591,6592,6593,6594]
cert_ridgeSupport_code_3 592
cert_ridgeSupport_rest_2 592 000 0
cert_ridgeSupport_rest_2 592 001 416
cert_ridgeSupport_rest_2 592 002 832
cert_ridgeSupport_rest_2 592 003 1248
cert_ridgeSupport_rest_2 592 004 1664
cert_ridgeSupport_rest_2 592 005 2080
cert_ridgeSupport_rest_2 592 006 2496
cert_ridgeSupport_rest_2 592 007 2912
cert_ridgeSupport_rest_2 592 008 3328
cert_ridgeSupport_rest_2 592 009 3497
cert_ridgeSupport_suffix_4 592 009
cert_ridgeSupport_suffix_3 592 008 009
cert_ridgeSupport_suffix_3 592 007 008
cert_ridgeSupport_suffix_3 592 006 007
cert_ridgeSupport_suffix_3 592 005 006
cert_ridgeSupport_suffix_3 592 004 005
cert_ridgeSupport_suffix_3 592 003 004
cert_ridgeSupport_suffix_3 592 002 003
cert_ridgeSupport_suffix_3 592 001 002
cert_ridgeSupport_suffix_3 592 000 001
cert_ridgeSupport_source_3 592 13 269
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
