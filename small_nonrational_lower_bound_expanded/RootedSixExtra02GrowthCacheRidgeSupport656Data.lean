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
def ridgeSupport656_000 : List Nat := [61,75,91,94,96,902,903,904,907,908,913,914,919,921,943,945,947,949,951,956,957,959,962,1037,1038,1041,1042,1045,1046,1083,1084,1085]
def ridgeSupport656_001 : List Nat := [1088,1089,1094,1095,1100,1102,1124,1126,1128,1130,1132,1137,1138,1140,1143,1275,1279,1280,1281,1282,1284,1285,1292,1294,1318,1320,1322,1323,1325,1327,1328,1332]
def ridgeSupport656_002 : List Nat := [1337,1338,1340,1342,1344,1345,1347,1349,1350,1354,1356,1361,1362,3164,3169,3178,3180,3246,3247,3256,3257,3262,3263,3266,3268,3272,3273,3279,3282,3294,3295,3304]
def ridgeSupport656_003 : List Nat := [3305,3332,3337,3342,3343,3346,3348,3352,3353,3358,3359,3368,3369,3382,3383,3392,3393,3404,3409,3418,3420,3486,3487,3496,3497,3502,3503,3506,3508,3512,3513,3519]
def ridgeSupport656_004 : List Nat := [3522,3534,3535,3544,3545,3572,3577,3582,3583,3586,3588,3592,3593,3598,3599,3608,3609,3622,3623,3632,3633,3712,3713,3716,3717,4532,4537,4546,4548,4566,4567,4576]
def ridgeSupport656_005 : List Nat := [4577,4614,4615,4624,4625,4630,4631,4634,4636,4640,4641,4647,4650,4652,4657,4662,4663,4666,4668,4672,4673,4710,4711,4720,4721,4734,4735,4744,4745,4816,4817,4824]
def ridgeSupport656_006 : List Nat := [4825,4918,4920,4948,4950,4958,4959,4976,4977,5060,5065,5090,5095,5104,5105,5122,5123,5240,5245,5246,5250,5252,5257,5258,5262,5313,5316,5319,5323,5332,5334,5342]
def ridgeSupport656_007 : List Nat := [5347,5602,5603,5638,5639,5800,5801,6246,6247,6256,6257,6261,6262,6263,6264,6269,6270,6294,6295,6304,6305,6309,6310,6311,6312,6317,6318,6506,6508,6519,6522,6537]
def ridgeSupport656_008 : List Nat := [6538,6539,6540,6545,6546,6572,6573,6575,6577,6609,6610,6611,6612]
cert_ridgeSupport_code_3 656
cert_ridgeSupport_rest_2 656 000 0
cert_ridgeSupport_rest_2 656 001 416
cert_ridgeSupport_rest_2 656 002 832
cert_ridgeSupport_rest_2 656 003 1248
cert_ridgeSupport_rest_2 656 004 1664
cert_ridgeSupport_rest_2 656 005 2080
cert_ridgeSupport_rest_2 656 006 2496
cert_ridgeSupport_rest_2 656 007 2912
cert_ridgeSupport_rest_2 656 008 3328
cert_ridgeSupport_rest_2 656 009 3497
cert_ridgeSupport_suffix_4 656 009
cert_ridgeSupport_suffix_3 656 008 009
cert_ridgeSupport_suffix_3 656 007 008
cert_ridgeSupport_suffix_3 656 006 007
cert_ridgeSupport_suffix_3 656 005 006
cert_ridgeSupport_suffix_3 656 004 005
cert_ridgeSupport_suffix_3 656 003 004
cert_ridgeSupport_suffix_3 656 002 003
cert_ridgeSupport_suffix_3 656 001 002
cert_ridgeSupport_suffix_3 656 000 001
cert_ridgeSupport_source_3 656 13 269
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
