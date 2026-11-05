module
prelude
public import RootedSixBase03GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport352_000 : List Nat := [52,72,92,102,111,113,553,554,555,556,563,564,709,710,711,712,719,720,853,855,857,859,861,866,867,869,872,895,896,900,902,903]
def ridgeSupport352_001 : List Nat := [907,909,910,912,974,975,976,977,984,985,1118,1120,1122,1124,1126,1131,1132,1134,1137,1160,1161,1165,1167,1168,1172,1174,1175,1177,1239,1240,1241,1242]
def ridgeSupport352_002 : List Nat := [1249,1250,1383,1385,1387,1389,1391,1396,1397,1399,1402,1425,1426,1430,1432,1433,1437,1439,1440,1442,1492,1494,1496,1498,1500,1505,1506,1508,1511,1534,1535,1539]
def ridgeSupport352_003 : List Nat := [1541,1542,1546,1548,1549,1551,1602,1604,1605,1607,1608,1610,1612,1613,1615,1616,1620,1621,3007,3010,3013,3017,3031,3034,3040,3041,3045,3047,3050,3051,3056,3057]
def ridgeSupport352_004 : List Nat := [3066,3067,3088,3089,3098,3099,3104,3105,3109,3111,3114,3115,3120,3125,3130,3131,3135,3137,3139,3142,3145,3149,3163,3166,3172,3173,3177,3179,3182,3183,3188,3189]
def ridgeSupport352_005 : List Nat := [3198,3199,3220,3221,3230,3231,3236,3237,3241,3243,3246,3247,3252,3257,3262,3263,3267,3269,3272,3273,3276,3281,3284,3285,3288,3293,3308,3309,3320,3321,3382,3383]
def ridgeSupport352_006 : List Nat := [3385,3387,3394,3395,3397,3399,3418,3419,3430,3431,3487,3490,3493,3497,3511,3514,3520,3521,3525,3527,3530,3531,3536,3537,3546,3547,3568,3569,3578,3579,3584,3585]
def ridgeSupport352_007 : List Nat := [3589,3591,3594,3595,3600,3605,3610,3611,3615,3617,3620,3621,3624,3629,3632,3633,3636,3641,3656,3657,3668,3669,3730,3731,3733,3735,3742,3743,3745,3747,3766,3767]
def ridgeSupport352_008 : List Nat := [3778,3779,3835,3838,3841,3845,3859,3862,3868,3869,3873,3875,3878,3879,3884,3885,3894,3895,3916,3917,3926,3927,3932,3933,3937,3939,3942,3943,3948,3953,3958,3959]
def ridgeSupport352_009 : List Nat := [3963,3965,3968,3969,3972,3977,3980,3981,3984,3989,4004,4005,4016,4017,4078,4079,4081,4083,4090,4091,4093,4095,4114,4115,4126,4127,4184,4185,4188,4193,4196,4197]
def ridgeSupport352_010 : List Nat := [4200,4205,4220,4221,4232,4233,4294,4295,4297,4299,4306,4307,4309,4311,4330,4331,4342,4343,4531,4534,4537,4541,4543,4546,4549,4553,4556,4557,4570,4571,4579,4582]
def ridgeSupport352_011 : List Nat := [4585,4589,4592,4593,4606,4607,4615,4618,4621,4625,4628,4629,4642,4643,4652,4653,4666,4667,5030,5031,5066,5067,5126,5127,5186,5187]
def ridgeSupport352_code : Nat := 0x2887442a03d01a7973ca9d3ce9a47723a916c8b244722290ac85242320d905481e3ff1fe8f8c7c23db1e98f3478e3b71da8e6c7323931c58e146fe37b1b98db46ce1ef0f6875c3aa1af0d5869c34a1970c9863c31a11308883ec1f20db068832c1920c305c82cc16203f01e809c049ffeffd7fdbfe9fe6ff17f7bfb9f62fb07d2be91f2af907c6be31f12f847c0be01efaf7b7bbbdd9ee2f6c7b3bd99ec6f617aebd71eaef567a6bd31e6ef36796bcb1e4ef26791bc85e3af1c78b3c4de0af0177f3bedd86ec275bbad9d46ea174fba79d2ee95749ba49caae54724b921c72e34718b8c1c5ae28712b891c42e1f70db869c2ae10705b829c0ee05700b801bf6dfa6f8b7c1bb6dda6e8b741b96dca6e3b715b82dc06dd36ddb52da56d1367daced666adb569a8ed456a1b509a76d3969bb4d99f2cf8676b3b19bacd866ab3519a2ccc664b32198acc365fb2f9972cb4657b2b9956ca9652b29193ec9e64ab2518fec7e63ab1d18dec6e635b1a58cac6462f316d89ac49623310d882c3f61db0e986ac30615b0a984ec25610b081836c1a608b0417f6bfa5f8afc17d6bea5f3af957c2be05ed2f5d792bc55e12efccaa654328193cc9a64c3251920c8e6453221908c1e60d3061828c0c60530197fcbfc5e72f21788bc25dc2ed1760bac5d42d11680b3e59d2cc9660b2c5922c895e8aee5752ba15bcada56b2b4959c9c44e126d13649b04d724c925c92c494248123c91a48924411c48dc46c23591988c846223011787b23d81e88f4079e3ce1c80e3871a38b1c38e187083801bf8da06ca3631b10d746b63591ab8d545a02cf1640b1c58c2c511a08cc45822b11508a40e206f0330170090034
def ridgeSupport352_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport352_code
def ridgeSupport352_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport352_code
def ridgeSupport352_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport352_code
def ridgeSupport352_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport352_code
def ridgeSupport352_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport352_code
def ridgeSupport352_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport352_code
def ridgeSupport352_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport352_code
def ridgeSupport352_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport352_code
def ridgeSupport352_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport352_code
def ridgeSupport352_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport352_code
def ridgeSupport352_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport352_code
def ridgeSupport352_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport352_code
def ridgeSupport352_rest_012 : Nat := PackedRawNatGrowth.drop 4914 ridgeSupport352_code
def ridgeSupport352_suffix_012 : List Nat := []
def ridgeSupport352_suffix_011 : List Nat := ridgeSupport352_011 ++ ridgeSupport352_suffix_012
def ridgeSupport352_suffix_010 : List Nat := ridgeSupport352_010 ++ ridgeSupport352_suffix_011
def ridgeSupport352_suffix_009 : List Nat := ridgeSupport352_009 ++ ridgeSupport352_suffix_010
def ridgeSupport352_suffix_008 : List Nat := ridgeSupport352_008 ++ ridgeSupport352_suffix_009
def ridgeSupport352_suffix_007 : List Nat := ridgeSupport352_007 ++ ridgeSupport352_suffix_008
def ridgeSupport352_suffix_006 : List Nat := ridgeSupport352_006 ++ ridgeSupport352_suffix_007
def ridgeSupport352_suffix_005 : List Nat := ridgeSupport352_005 ++ ridgeSupport352_suffix_006
def ridgeSupport352_suffix_004 : List Nat := ridgeSupport352_004 ++ ridgeSupport352_suffix_005
def ridgeSupport352_suffix_003 : List Nat := ridgeSupport352_003 ++ ridgeSupport352_suffix_004
def ridgeSupport352_suffix_002 : List Nat := ridgeSupport352_002 ++ ridgeSupport352_suffix_003
def ridgeSupport352_suffix_001 : List Nat := ridgeSupport352_001 ++ ridgeSupport352_suffix_002
def ridgeSupport352_suffix_000 : List Nat := ridgeSupport352_000 ++ ridgeSupport352_suffix_001
theorem ridgeSupport352_source : candidateSupports 352 =
    (PackedRawNatGrowth.readList 13 378 ridgeSupport352_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
