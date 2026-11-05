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
def ridgeSupport416_000 : List Nat := [54,74,94,104,111,114,577,578,579,580,587,588,733,734,735,736,743,744,854,855,856,859,860,865,866,871,873,916,917,921,923,924]
def ridgeSupport416_001 : List Nat := [928,930,931,933,998,999,1000,1001,1008,1009,1119,1120,1121,1124,1125,1130,1131,1136,1138,1181,1182,1186,1188,1189,1193,1195,1196,1198,1263,1264,1265,1266]
def ridgeSupport416_002 : List Nat := [1273,1274,1384,1385,1386,1389,1390,1395,1396,1401,1403,1446,1447,1451,1453,1454,1458,1460,1461,1463,1493,1494,1495,1498,1499,1504,1505,1510,1512,1555,1556,1560]
def ridgeSupport416_003 : List Nat := [1562,1563,1567,1569,1570,1572,1601,1604,1605,1606,1609,1610,1611,1613,1618,1619,1621,1622,3007,3009,3014,3016,3034,3035,3037,3040,3043,3046,3048,3049,3062,3063]
def ridgeSupport416_004 : List Nat := [3068,3069,3082,3083,3096,3097,3103,3105,3110,3111,3116,3117,3122,3124,3127,3128,3135,3136,3139,3141,3146,3148,3166,3167,3169,3172,3175,3178,3180,3181,3194,3195]
def ridgeSupport416_005 : List Nat := [3200,3201,3214,3215,3228,3229,3235,3237,3242,3243,3248,3249,3254,3256,3259,3260,3267,3268,3270,3271,3278,3280,3282,3283,3290,3292,3306,3307,3318,3319,3436,3437]
def ridgeSupport416_006 : List Nat := [3439,3441,3448,3449,3451,3453,3472,3473,3484,3485,3487,3489,3494,3496,3514,3515,3517,3520,3523,3526,3528,3529,3542,3543,3548,3549,3562,3563,3576,3577,3583,3585]
def ridgeSupport416_007 : List Nat := [3590,3591,3596,3597,3602,3604,3607,3608,3615,3616,3618,3619,3626,3628,3630,3631,3638,3640,3654,3655,3666,3667,3784,3785,3787,3789,3796,3797,3799,3801,3820,3821]
def ridgeSupport416_008 : List Nat := [3832,3833,3835,3837,3842,3844,3862,3863,3865,3868,3871,3874,3876,3877,3890,3891,3896,3897,3910,3911,3924,3925,3931,3933,3938,3939,3944,3945,3950,3952,3955,3956]
def ridgeSupport416_009 : List Nat := [3963,3964,3966,3967,3974,3976,3978,3979,3986,3988,4002,4003,4014,4015,4132,4133,4135,4137,4144,4145,4147,4149,4168,4169,4180,4181,4182,4183,4190,4192,4194,4195]
def ridgeSupport416_010 : List Nat := [4202,4204,4218,4219,4230,4231,4348,4349,4351,4353,4360,4361,4363,4365,4384,4385,4396,4397,4531,4533,4538,4540,4543,4545,4550,4552,4554,4555,4576,4577,4579,4581]
def ridgeSupport416_011 : List Nat := [4586,4588,4590,4591,4612,4613,4615,4617,4622,4624,4626,4627,4648,4649,4650,4651,4672,4673,5026,5027,5062,5063,5122,5123,5182,5183]
def ridgeSupport416_code : Nat := 0x287f43ea01d00a78f3c69d1ce8a483240915c8aa453228909c84a42120e904c81e40b2048f7c7ba3d91ea8f2c78e3c31e08e5c72a3911c68e0c6fe3791ba8dac6ce25b12c890c48221b10b884c4222030ff87ec3f210f08683dc1ea0d906a831c18a0c105e82bc15a0ab054824c12206b033818c0c2053027812c091f5efae7d1be89f28f927c5be29f10f867bfbdf9ef8f7b7ba3dcdee0f6e7b4bda1ec6f627aebd6deaaf547a3bd19e72f38799bcc9e4af247913c7de38f1978bbc59e08f0277ebbeddf2ef8776bbb1db2ed776abb51d9aecb764bb21ca6e52723b919c70e36717b8b9c58e2a711b889c40e1f70c385dc28e12706b831c0ee06700b7fdbf2df86f5b7a9bbaddc6ebb759b92dc86e3370db80dbd6ddb6e9b50da66d0b67db3ad9c6c8b641afad7b6bcb5e1ae2d6f6b6b5b19eecf6675b3a99b8cda669b3499a0cce663b319988cc365e32ed970cb6658b2c1956caa652b28d93ac9c647b239902c8063db1e98dac6c635319d8c8c6162fb179898c4a622b10d880c3f61c30dd868c32616b0b184ec26610b07d832c18605b0297fabfc5fbafd97d2be85f32f8d7c0bdd5edaf69790bc65e0aefccac6553299948c9a64b3251924c8c6453221904c48622310987cc3661a30c1850c265e82f31784bc05db2ed175cbac5d52db96d4b685b22d716b4b565a72d315ecaf25742b995b8ada56a2b495a09f44f927913c49e04ef25712b09564a9252929094449e24e91c88e046b23511948c8461230117c7e23f01f48fa07ce3e61d28e8c7443a01ce0e6c7323951ca0da46ce3621b08d706b63581ab8d585d02e71700b7c5bc2dd126092c48824312109040e406f0340178094036
def ridgeSupport416_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport416_code
def ridgeSupport416_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport416_code
def ridgeSupport416_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport416_code
def ridgeSupport416_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport416_code
def ridgeSupport416_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport416_code
def ridgeSupport416_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport416_code
def ridgeSupport416_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport416_code
def ridgeSupport416_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport416_code
def ridgeSupport416_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport416_code
def ridgeSupport416_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport416_code
def ridgeSupport416_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport416_code
def ridgeSupport416_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport416_code
def ridgeSupport416_rest_012 : Nat := PackedRawNatGrowth.drop 4914 ridgeSupport416_code
def ridgeSupport416_suffix_012 : List Nat := []
def ridgeSupport416_suffix_011 : List Nat := ridgeSupport416_011 ++ ridgeSupport416_suffix_012
def ridgeSupport416_suffix_010 : List Nat := ridgeSupport416_010 ++ ridgeSupport416_suffix_011
def ridgeSupport416_suffix_009 : List Nat := ridgeSupport416_009 ++ ridgeSupport416_suffix_010
def ridgeSupport416_suffix_008 : List Nat := ridgeSupport416_008 ++ ridgeSupport416_suffix_009
def ridgeSupport416_suffix_007 : List Nat := ridgeSupport416_007 ++ ridgeSupport416_suffix_008
def ridgeSupport416_suffix_006 : List Nat := ridgeSupport416_006 ++ ridgeSupport416_suffix_007
def ridgeSupport416_suffix_005 : List Nat := ridgeSupport416_005 ++ ridgeSupport416_suffix_006
def ridgeSupport416_suffix_004 : List Nat := ridgeSupport416_004 ++ ridgeSupport416_suffix_005
def ridgeSupport416_suffix_003 : List Nat := ridgeSupport416_003 ++ ridgeSupport416_suffix_004
def ridgeSupport416_suffix_002 : List Nat := ridgeSupport416_002 ++ ridgeSupport416_suffix_003
def ridgeSupport416_suffix_001 : List Nat := ridgeSupport416_001 ++ ridgeSupport416_suffix_002
def ridgeSupport416_suffix_000 : List Nat := ridgeSupport416_000 ++ ridgeSupport416_suffix_001
theorem ridgeSupport416_source : candidateSupports 416 =
    (PackedRawNatGrowth.readList 13 378 ridgeSupport416_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
