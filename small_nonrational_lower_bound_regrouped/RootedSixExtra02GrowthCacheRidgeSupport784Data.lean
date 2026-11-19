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
def ridgeSupport784_000 : List Nat := [62,76,92,95,96,923,924,925,928,929,934,935,940,942,944,945,946,949,950,955,956,961,963,1049,1050,1053,1054,1057,1058,1104,1105,1106]
def ridgeSupport784_001 : List Nat := [1109,1110,1115,1116,1121,1123,1125,1126,1127,1130,1131,1136,1137,1142,1144,1296,1300,1301,1302,1303,1305,1306,1313,1315,1317,1321,1322,1323,1324,1326,1327,1334]
def ridgeSupport784_002 : List Nat := [1336,1338,1339,1343,1344,1345,1346,1348,1349,1357,1359,1360,1362,3166,3168,3172,3174,3252,3253,3258,3259,3260,3261,3266,3267,3272,3274,3278,3280,3300,3301,3306]
def ridgeSupport784_003 : List Nat := [3307,3334,3336,3340,3342,3348,3349,3354,3355,3356,3357,3362,3363,3380,3381,3386,3387,3406,3408,3412,3414,3492,3493,3498,3499,3500,3501,3506,3507,3512,3514,3518]
def ridgeSupport784_004 : List Nat := [3520,3540,3541,3546,3547,3574,3576,3580,3582,3588,3589,3594,3595,3596,3597,3602,3603,3620,3621,3626,3627,3728,3729,3732,3733,4534,4536,4540,4542,4572,4573,4578]
def ridgeSupport784_005 : List Nat := [4579,4620,4621,4626,4627,4628,4629,4634,4635,4640,4642,4646,4648,4654,4656,4660,4662,4668,4669,4674,4675,4716,4717,4722,4723,4740,4741,4746,4747,4832,4833,4840]
def ridgeSupport784_006 : List Nat := [4841,4990,4992,5020,5022,5030,5031,5048,5049,5062,5064,5092,5094,5102,5103,5120,5121,5242,5244,5246,5248,5254,5256,5258,5260,5315,5317,5319,5321,5338,5340,5344]
def ridgeSupport784_007 : List Nat := [5346,5600,5601,5636,5637,5802,5803,6252,6253,6258,6259,6260,6261,6263,6265,6266,6267,6300,6301,6306,6307,6308,6309,6311,6313,6314,6315,6512,6514,6518,6520,6536]
def ridgeSupport784_008 : List Nat := [6537,6539,6541,6542,6543,6590,6591,6593,6595,6608,6609,6611,6613]
cert_ridgeSupport_code_3 784
cert_ridgeSupport_rest_2 784 000 0
cert_ridgeSupport_rest_2 784 001 416
cert_ridgeSupport_rest_2 784 002 832
cert_ridgeSupport_rest_2 784 003 1248
cert_ridgeSupport_rest_2 784 004 1664
cert_ridgeSupport_rest_2 784 005 2080
cert_ridgeSupport_rest_2 784 006 2496
cert_ridgeSupport_rest_2 784 007 2912
cert_ridgeSupport_rest_2 784 008 3328
cert_ridgeSupport_rest_2 784 009 3497
cert_ridgeSupport_suffix_4 784 009
cert_ridgeSupport_suffix_3 784 008 009
cert_ridgeSupport_suffix_3 784 007 008
cert_ridgeSupport_suffix_3 784 006 007
cert_ridgeSupport_suffix_3 784 005 006
cert_ridgeSupport_suffix_3 784 004 005
cert_ridgeSupport_suffix_3 784 003 004
cert_ridgeSupport_suffix_3 784 002 003
cert_ridgeSupport_suffix_3 784 001 002
cert_ridgeSupport_suffix_3 784 000 001
cert_ridgeSupport_source_3 784 13 269
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
