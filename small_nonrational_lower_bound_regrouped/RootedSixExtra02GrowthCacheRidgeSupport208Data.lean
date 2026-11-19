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
def ridgeSupport208_000 : List Nat := [57,71,87,93,94,880,881,885,887,888,892,894,895,897,901,902,906,908,909,913,915,916,918,989,990,993,994,997,998,1061,1062,1066]
def ridgeSupport208_001 : List Nat := [1068,1069,1073,1075,1076,1078,1082,1083,1087,1089,1090,1094,1096,1097,1099,1256,1257,1258,1261,1262,1263,1265,1270,1272,1277,1278,1279,1282,1283,1284,1286,1291]
def ridgeSupport208_002 : List Nat := [1293,1340,1341,1343,1344,1345,1346,1348,1349,1351,1352,1354,1355,3177,3179,3183,3185,3236,3237,3242,3243,3263,3265,3269,3271,3276,3277,3282,3283,3284,3285,3290]
def ridgeSupport208_003 : List Nat := [3291,3332,3333,3338,3339,3345,3347,3351,3353,3372,3373,3378,3379,3396,3397,3402,3403,3417,3419,3423,3425,3476,3477,3482,3483,3503,3505,3509,3511,3516,3517,3522]
def ridgeSupport208_004 : List Nat := [3523,3524,3525,3530,3531,3572,3573,3578,3579,3585,3587,3591,3593,3612,3613,3618,3619,3636,3637,3642,3643,3648,3649,3652,3653,4545,4547,4551,4553,4556,4557,4562]
def ridgeSupport208_005 : List Nat := [4563,4604,4605,4610,4611,4631,4633,4637,4639,4644,4645,4650,4651,4652,4653,4658,4659,4665,4667,4671,4673,4700,4701,4706,4707,4724,4725,4730,4731,4752,4753,4760]
def ridgeSupport208_006 : List Nat := [4761,4845,4847,4875,4877,4890,4891,4908,4909,4917,4919,4947,4949,4962,4963,4980,4981,5243,5245,5247,5249,5255,5257,5259,5261,5314,5316,5318,5320,5325,5327,5331]
def ridgeSupport208_007 : List Nat := [5333,5610,5611,5646,5647,5792,5793,6236,6237,6242,6243,6260,6261,6266,6267,6270,6271,6284,6285,6290,6291,6308,6309,6314,6315,6318,6319,6503,6505,6509,6511,6536]
def ridgeSupport208_008 : List Nat := [6537,6542,6543,6546,6547,6554,6556,6558,6559,6572,6574,6576,6577]
cert_ridgeSupport_code_3 208
cert_ridgeSupport_rest_2 208 000 0
cert_ridgeSupport_rest_2 208 001 416
cert_ridgeSupport_rest_2 208 002 832
cert_ridgeSupport_rest_2 208 003 1248
cert_ridgeSupport_rest_2 208 004 1664
cert_ridgeSupport_rest_2 208 005 2080
cert_ridgeSupport_rest_2 208 006 2496
cert_ridgeSupport_rest_2 208 007 2912
cert_ridgeSupport_rest_2 208 008 3328
cert_ridgeSupport_rest_2 208 009 3497
cert_ridgeSupport_suffix_4 208 009
cert_ridgeSupport_suffix_3 208 008 009
cert_ridgeSupport_suffix_3 208 007 008
cert_ridgeSupport_suffix_3 208 006 007
cert_ridgeSupport_suffix_3 208 005 006
cert_ridgeSupport_suffix_3 208 004 005
cert_ridgeSupport_suffix_3 208 003 004
cert_ridgeSupport_suffix_3 208 002 003
cert_ridgeSupport_suffix_3 208 001 002
cert_ridgeSupport_suffix_3 208 000 001
cert_ridgeSupport_source_3 208 13 269
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
