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
def ridgeSupport400_000 : List Nat := [60,74,90,93,96,881,882,883,886,887,892,893,898,900,943,944,948,950,951,955,957,958,960,1025,1026,1029,1030,1033,1034,1062,1063,1064]
def ridgeSupport400_001 : List Nat := [1067,1068,1073,1074,1079,1081,1124,1125,1129,1131,1132,1136,1138,1139,1141,1254,1258,1259,1260,1261,1263,1264,1271,1273,1319,1320,1321,1324,1325,1326,1328,1333]
def ridgeSupport400_002 : List Nat := [1335,1338,1341,1342,1343,1346,1347,1348,1350,1355,1356,1358,1359,3165,3167,3184,3186,3244,3245,3250,3251,3264,3265,3267,3270,3273,3276,3278,3279,3292,3293,3298]
def ridgeSupport400_003 : List Nat := [3299,3333,3335,3340,3341,3346,3347,3352,3354,3360,3361,3374,3375,3384,3385,3398,3399,3405,3407,3424,3426,3484,3485,3490,3491,3504,3505,3507,3510,3513,3516,3518]
def ridgeSupport400_004 : List Nat := [3519,3532,3533,3538,3539,3573,3575,3580,3581,3586,3587,3592,3594,3600,3601,3614,3615,3624,3625,3638,3639,3696,3697,3700,3701,4533,4535,4552,4554,4564,4565,4570]
def ridgeSupport400_005 : List Nat := [4571,4612,4613,4618,4619,4632,4633,4635,4638,4641,4644,4646,4647,4653,4655,4660,4661,4666,4667,4672,4674,4708,4709,4714,4715,4732,4733,4738,4739,4800,4801,4808]
def ridgeSupport400_006 : List Nat := [4809,4846,4848,4876,4878,4886,4887,4904,4905,5061,5063,5091,5093,5106,5107,5124,5125,5241,5243,5248,5250,5253,5255,5260,5262,5312,5314,5321,5323,5326,5328,5343]
def ridgeSupport400_007 : List Nat := [5345,5604,5605,5640,5641,5798,5799,6244,6245,6250,6251,6260,6262,6264,6265,6268,6271,6292,6293,6298,6299,6308,6310,6312,6313,6316,6319,6507,6510,6513,6516,6536]
def ridgeSupport400_008 : List Nat := [6538,6540,6541,6544,6547,6554,6555,6557,6559,6608,6610,6612,6613]
cert_ridgeSupport_code_3 400
cert_ridgeSupport_rest_2 400 000 0
cert_ridgeSupport_rest_2 400 001 416
cert_ridgeSupport_rest_2 400 002 832
cert_ridgeSupport_rest_2 400 003 1248
cert_ridgeSupport_rest_2 400 004 1664
cert_ridgeSupport_rest_2 400 005 2080
cert_ridgeSupport_rest_2 400 006 2496
cert_ridgeSupport_rest_2 400 007 2912
cert_ridgeSupport_rest_2 400 008 3328
cert_ridgeSupport_rest_2 400 009 3497
cert_ridgeSupport_suffix_4 400 009
cert_ridgeSupport_suffix_3 400 008 009
cert_ridgeSupport_suffix_3 400 007 008
cert_ridgeSupport_suffix_3 400 006 007
cert_ridgeSupport_suffix_3 400 005 006
cert_ridgeSupport_suffix_3 400 004 005
cert_ridgeSupport_suffix_3 400 003 004
cert_ridgeSupport_suffix_3 400 002 003
cert_ridgeSupport_suffix_3 400 001 002
cert_ridgeSupport_suffix_3 400 000 001
cert_ridgeSupport_source_3 400 13 269
end Papers.RationalityTen.RootedCaches.RootedSixExtra02
