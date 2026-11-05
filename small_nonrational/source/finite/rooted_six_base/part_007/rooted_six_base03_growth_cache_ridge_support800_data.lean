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
def ridgeSupport800_000 : List Nat := [56,76,96,106,113,114,601,602,603,604,611,612,757,758,759,760,767,768,896,897,898,901,902,907,908,913,915,917,918,919,922,923]
def ridgeSupport800_001 : List Nat := [928,929,934,936,1022,1023,1024,1025,1032,1033,1161,1162,1163,1166,1167,1172,1173,1178,1180,1182,1183,1184,1187,1188,1193,1194,1199,1201,1287,1288,1289,1290]
def ridgeSupport800_002 : List Nat := [1297,1298,1426,1427,1428,1431,1432,1437,1438,1443,1445,1447,1448,1449,1452,1453,1458,1459,1464,1466,1535,1536,1537,1540,1541,1546,1547,1552,1554,1556,1557,1558]
def ridgeSupport800_003 : List Nat := [1561,1562,1567,1568,1573,1575,1601,1602,1606,1607,1608,1609,1611,1612,1620,1622,1623,1625,3008,3010,3012,3014,3030,3031,3036,3037,3042,3044,3048,3050,3070,3071]
def ridgeSupport800_004 : List Nat := [3076,3077,3078,3079,3084,3085,3104,3106,3110,3112,3118,3119,3124,3125,3126,3127,3129,3130,3140,3142,3144,3146,3162,3163,3168,3169,3174,3176,3180,3182,3202,3203]
def ridgeSupport800_005 : List Nat := [3208,3209,3210,3211,3216,3217,3236,3238,3242,3244,3250,3251,3256,3257,3258,3259,3261,3262,3378,3379,3386,3388,3390,3391,3398,3400,3414,3415,3426,3427,3432,3433]
def ridgeSupport800_006 : List Nat := [3440,3442,3444,3445,3452,3454,3468,3469,3480,3481,3488,3490,3492,3494,3510,3511,3516,3517,3522,3524,3528,3530,3550,3551,3556,3557,3558,3559,3564,3565,3584,3586]
def ridgeSupport800_007 : List Nat := [3590,3592,3598,3599,3604,3605,3606,3607,3609,3610,3726,3727,3734,3736,3738,3739,3746,3748,3762,3763,3774,3775,3780,3781,3788,3790,3792,3793,3800,3802,3816,3817]
def ridgeSupport800_008 : List Nat := [3828,3829,3836,3838,3840,3842,3858,3859,3864,3865,3870,3872,3876,3878,3898,3899,3904,3905,3906,3907,3912,3913,3932,3934,3938,3940,3946,3947,3952,3953,3954,3955]
def ridgeSupport800_009 : List Nat := [3957,3958,4074,4075,4082,4084,4086,4087,4094,4096,4110,4111,4122,4123,4128,4129,4136,4138,4140,4141,4148,4150,4164,4165,4176,4177,4290,4291,4298,4300,4302,4303]
def ridgeSupport800_010 : List Nat := [4310,4312,4326,4327,4338,4339,4344,4345,4352,4354,4356,4357,4364,4366,4380,4381,4392,4393,4532,4534,4536,4538,4544,4546,4548,4550,4566,4567,4572,4573,4580,4582]
def ridgeSupport800_011 : List Nat := [4584,4586,4602,4603,4608,4609,4616,4618,4620,4622,4638,4639,4644,4645,4662,4663,4668,4669,5022,5023,5058,5059,5118,5119,5178,5179]
def ridgeSupport800_code : Nat := 0x287743a9ffcffa7873c29cfce7a47b23c91bc8da44b22490fc87a41d20c90548224032008fdc7ea3d51e88f347923bb1dc8ebc75a38d1c48e147023751b88db46d225312888ec47221d10c882c41220510087cc3e21e70f2873c39a1b10d6867c33a1990ca861c30a0a3050822c11206d034816c0b2055028810c08203701a807c03a000ffe7fbbfd9fe8ff27f5bfa9eecf757b9bdc9ee2f707b5bda9ec8f627af3d71e92f487a1bd09e82f4079dbce9e4cf247903c79e32f18789bc49e04f0077f3bf1deaef4774bba1db4ed8768bb41d9cecc762bb11d7eebe759bac9d48ea274dba69d30e96747ba39c34e1970bb859c2ae14707b839c10e067013801bdadec6f3b799bcade46efb779b94dc86e23709b7adbc6dbb6d9b4cda46d13681b32d986c6b631afcd7c6bab5d1ae4d706b4b5a1ac6d626abb559a90d4669fb4f9a78d3a699b4c997ccbd65db2e9972cb8659b2c9958caa6533291922c90645b229912c88641b2098dcc6c63431998c2c6062db169894c486233111874c3961bb0d986ac34617b0b9850c26611308181ac0c603b01980ac045ffaff97d4be85f22f897babdc5ebaf5978cbc45e12f00cb265732b1950c9864b3249920c8e6463211904c4e625310187cc3461930b1854c28612308182cc146053021804c005ff2dd16e0b665b22d696b0b525a82d39694b4659e2ce9660b2e5942c99648a245112851424a1050725892bc9544a9252128c94049f24f127093449524a123c91c48b245122481240820090007fe3fe1d40e987423a01cd8e6872e3961ca8e4c72238c1c58e1870a3821c08e006002ff17c0bdc5ec2f5132098c4b825b12d09640e40710350180098038
def ridgeSupport800_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport800_code
def ridgeSupport800_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport800_code
def ridgeSupport800_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport800_code
def ridgeSupport800_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport800_code
def ridgeSupport800_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport800_code
def ridgeSupport800_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport800_code
def ridgeSupport800_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport800_code
def ridgeSupport800_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport800_code
def ridgeSupport800_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport800_code
def ridgeSupport800_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport800_code
def ridgeSupport800_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport800_code
def ridgeSupport800_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport800_code
def ridgeSupport800_rest_012 : Nat := PackedRawNatGrowth.drop 4914 ridgeSupport800_code
def ridgeSupport800_suffix_012 : List Nat := []
def ridgeSupport800_suffix_011 : List Nat := ridgeSupport800_011 ++ ridgeSupport800_suffix_012
def ridgeSupport800_suffix_010 : List Nat := ridgeSupport800_010 ++ ridgeSupport800_suffix_011
def ridgeSupport800_suffix_009 : List Nat := ridgeSupport800_009 ++ ridgeSupport800_suffix_010
def ridgeSupport800_suffix_008 : List Nat := ridgeSupport800_008 ++ ridgeSupport800_suffix_009
def ridgeSupport800_suffix_007 : List Nat := ridgeSupport800_007 ++ ridgeSupport800_suffix_008
def ridgeSupport800_suffix_006 : List Nat := ridgeSupport800_006 ++ ridgeSupport800_suffix_007
def ridgeSupport800_suffix_005 : List Nat := ridgeSupport800_005 ++ ridgeSupport800_suffix_006
def ridgeSupport800_suffix_004 : List Nat := ridgeSupport800_004 ++ ridgeSupport800_suffix_005
def ridgeSupport800_suffix_003 : List Nat := ridgeSupport800_003 ++ ridgeSupport800_suffix_004
def ridgeSupport800_suffix_002 : List Nat := ridgeSupport800_002 ++ ridgeSupport800_suffix_003
def ridgeSupport800_suffix_001 : List Nat := ridgeSupport800_001 ++ ridgeSupport800_suffix_002
def ridgeSupport800_suffix_000 : List Nat := ridgeSupport800_000 ++ ridgeSupport800_suffix_001
theorem ridgeSupport800_source : candidateSupports 800 =
    (PackedRawNatGrowth.readList 13 378 ridgeSupport800_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
