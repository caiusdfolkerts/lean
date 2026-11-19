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
def ridgeSupport336_000 : List Nat := [58,72,88,93,95,880,882,884,886,888,893,894,896,899,922,923,927,929,930,934,936,937,939,1001,1002,1005,1006,1009,1010,1061,1063,1065]
def ridgeSupport336_001 : List Nat := [1067,1069,1074,1075,1077,1080,1103,1104,1108,1110,1111,1115,1117,1118,1120,1255,1257,1259,1260,1262,1264,1265,1269,1274,1298,1299,1300,1303,1304,1305,1307,1312]
def ridgeSupport336_002 : List Nat := [1314,1339,1341,1342,1344,1345,1347,1349,1350,1352,1353,1357,1358,3171,3173,3182,3187,3238,3239,3248,3249,3261,3264,3270,3271,3275,3277,3280,3281,3286,3287,3296]
def ridgeSupport336_003 : List Nat := [3297,3334,3335,3339,3341,3344,3345,3350,3355,3366,3367,3376,3377,3390,3391,3400,3401,3411,3413,3422,3427,3478,3479,3488,3489,3501,3504,3510,3511,3515,3517,3520]
def ridgeSupport336_004 : List Nat := [3521,3526,3527,3536,3537,3574,3575,3579,3581,3584,3585,3590,3595,3606,3607,3616,3617,3630,3631,3640,3641,3664,3665,3668,3669,4539,4541,4550,4555,4558,4559,4568]
def ridgeSupport336_005 : List Nat := [4569,4606,4607,4616,4617,4629,4632,4638,4639,4643,4645,4648,4649,4654,4655,4659,4661,4664,4665,4670,4675,4702,4703,4712,4713,4726,4727,4736,4737,4768,4769,4776]
def ridgeSupport336_006 : List Nat := [4777,4844,4849,4874,4879,4888,4889,4906,4907,4989,4991,5019,5021,5034,5035,5052,5053,5241,5244,5247,5251,5253,5256,5259,5263,5312,5317,5318,5322,5324,5329,5337]
def ridgeSupport336_007 : List Nat := [5339,5608,5609,5644,5645,5794,5795,6238,6239,6248,6249,6262,6263,6266,6268,6269,6270,6286,6287,6296,6297,6310,6311,6314,6316,6317,6318,6501,6504,6515,6517,6538]
def ridgeSupport336_008 : List Nat := [6539,6542,6544,6545,6546,6555,6556,6557,6558,6590,6592,6594,6595]
cert_ridgeSupport_code_3 336
cert_ridgeSupport_rest_2 336 000 0
cert_ridgeSupport_rest_2 336 001 416
cert_ridgeSupport_rest_2 336 002 832
cert_ridgeSupport_rest_2 336 003 1248
cert_ridgeSupport_rest_2 336 004 1664
cert_ridgeSupport_rest_2 336 005 2080
cert_ridgeSupport_rest_2 336 006 2496
cert_ridgeSupport_rest_2 336 007 2912
cert_ridgeSupport_rest_2 336 008 3328
cert_ridgeSupport_rest_2 336 009 3497
cert_ridgeSupport_suffix_4 336 009
cert_ridgeSupport_suffix_3 336 008 009
cert_ridgeSupport_suffix_3 336 007 008
cert_ridgeSupport_suffix_3 336 006 007
cert_ridgeSupport_suffix_3 336 005 006
cert_ridgeSupport_suffix_3 336 004 005
cert_ridgeSupport_suffix_3 336 003 004
cert_ridgeSupport_suffix_3 336 002 003
cert_ridgeSupport_suffix_3 336 001 002
cert_ridgeSupport_suffix_3 336 000 001
cert_ridgeSupport_source_3 336 13 269
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
