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
def ridgeSupport672_000 : List Nat := [55,75,95,105,112,114,589,590,591,592,599,600,745,746,747,748,755,756,875,876,877,880,881,886,887,892,894,916,918,920,922,924]
def ridgeSupport672_001 : List Nat := [929,930,932,935,1010,1011,1012,1013,1020,1021,1140,1141,1142,1145,1146,1151,1152,1157,1159,1181,1183,1185,1187,1189,1194,1195,1197,1200,1275,1276,1277,1278]
def ridgeSupport672_002 : List Nat := [1285,1286,1405,1406,1407,1410,1411,1416,1417,1422,1424,1446,1448,1450,1452,1454,1459,1460,1462,1465,1514,1515,1516,1519,1520,1525,1526,1531,1533,1555,1557,1559]
def ridgeSupport672_003 : List Nat := [1561,1563,1568,1569,1571,1574,1601,1603,1605,1607,1608,1610,1612,1613,1617,1619,1624,1625,3006,3011,3012,3016,3032,3033,3036,3038,3042,3043,3049,3052,3064,3065]
def ridgeSupport672_004 : List Nat := [3074,3075,3080,3081,3090,3091,3102,3107,3112,3113,3116,3118,3122,3123,3126,3128,3132,3133,3138,3143,3144,3148,3164,3165,3168,3170,3174,3175,3181,3184,3196,3197]
def ridgeSupport672_005 : List Nat := [3206,3207,3212,3213,3222,3223,3234,3239,3244,3245,3248,3250,3254,3255,3258,3260,3264,3265,3324,3325,3332,3334,3336,3337,3344,3346,3360,3361,3372,3373,3434,3435]
def ridgeSupport672_006 : List Nat := [3438,3443,3446,3447,3450,3455,3470,3471,3482,3483,3486,3491,3492,3496,3512,3513,3516,3518,3522,3523,3529,3532,3544,3545,3554,3555,3560,3561,3570,3571,3582,3587]
def ridgeSupport672_007 : List Nat := [3592,3593,3596,3598,3602,3603,3606,3608,3612,3613,3672,3673,3680,3682,3684,3685,3692,3694,3708,3709,3720,3721,3782,3783,3786,3791,3794,3795,3798,3803,3818,3819]
def ridgeSupport672_008 : List Nat := [3830,3831,3834,3839,3840,3844,3860,3861,3864,3866,3870,3871,3877,3880,3892,3893,3902,3903,3908,3909,3918,3919,3930,3935,3940,3941,3944,3946,3950,3951,3954,3956]
def ridgeSupport672_009 : List Nat := [3960,3961,4020,4021,4028,4030,4032,4033,4040,4042,4056,4057,4068,4069,4130,4131,4134,4139,4142,4143,4146,4151,4166,4167,4178,4179,4236,4237,4244,4246,4248,4249]
def ridgeSupport672_010 : List Nat := [4256,4258,4272,4273,4284,4285,4346,4347,4350,4355,4358,4359,4362,4367,4382,4383,4394,4395,4530,4535,4536,4540,4542,4547,4548,4552,4560,4561,4574,4575,4578,4583]
def ridgeSupport672_011 : List Nat := [4584,4588,4596,4597,4610,4611,4614,4619,4620,4624,4632,4633,4646,4647,4656,4657,4670,4671,5024,5025,5060,5061,5120,5121,5180,5181]
def ridgeSupport672_code : Nat := 0x287b43ca00d00278b3c49d0ce8247f23e918c8c244f22690cc86242120c905c81a4072028fac7d23d91e88f3c78a3bf1de8e8c7423911c48e1c6fa3791b88dbc6ca25712a88fc47a21f10a883c41a2070fe87dc3ea17b0bc858c2c21450a084cc26212d094846c2320a7052823c11a06f032817c0ba057026811c089fcafe47ecbf61f94fc87e0bf01f7cfbc7dabed1ef2f787ba3dc9edef6e7b53da1ecaf647afbd69e9ef4e7a2bd11e7ef3e79abcd1e50f2578fbc79e34f1878abc51e08f0077fbbe9deeef6775bba9db6ed6769bb49d9eeca763bb19d12e8873eb9f1cdce6c732b991cc4e6072cb961c3ae1c70c3859c26e127073831c12e08701b7f9be6df26f4b7a1bc6de26ecb761b98dc96e1b709b7cdbc6dcb6e1b50da46d1b679b36d9a6c7b639afed7a6bbb5d9ae6d6e6b5b5a9a5ad2c690b481a24d10684b421a0cd0467eb3f1982cc065e32e996ecb665932c195acac653b28992ec96646b23190ec8663eb1f18e0c6d633b1998c4c6062eb171898c48623b10987ac3c61c30d9866c3261730b1852c28611b079826c12604b021806c025fcafe17d8be95f1af897bcbdc5ecaf61790bc45e1aef8cb26583299944c9a64c3251920c8e6453219904c4c6233109880c3661930b9854c265fd2fd97d8bea5f02f797b0bd65ea2dc96d8b685b32d716b0b545a82d31640b1c5892c4160cb0457f2bf15f4a0c50527f13f49f84fb25812b49564aa252928c94249f24e921c90a48023f91e88f247623a91d07fa3fc1fa8fd07e63f21d38e907443a11ce0e687303961ca0df86f83771bb0dc46e036d1b60dac5e82f31760bac5d42e912c095c4a024f12709340e4070034817c096037
def ridgeSupport672_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport672_code
def ridgeSupport672_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport672_code
def ridgeSupport672_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport672_code
def ridgeSupport672_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport672_code
def ridgeSupport672_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport672_code
def ridgeSupport672_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport672_code
def ridgeSupport672_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport672_code
def ridgeSupport672_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport672_code
def ridgeSupport672_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport672_code
def ridgeSupport672_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport672_code
def ridgeSupport672_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport672_code
def ridgeSupport672_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport672_code
def ridgeSupport672_rest_012 : Nat := PackedRawNatGrowth.drop 4914 ridgeSupport672_code
def ridgeSupport672_suffix_012 : List Nat := []
def ridgeSupport672_suffix_011 : List Nat := ridgeSupport672_011 ++ ridgeSupport672_suffix_012
def ridgeSupport672_suffix_010 : List Nat := ridgeSupport672_010 ++ ridgeSupport672_suffix_011
def ridgeSupport672_suffix_009 : List Nat := ridgeSupport672_009 ++ ridgeSupport672_suffix_010
def ridgeSupport672_suffix_008 : List Nat := ridgeSupport672_008 ++ ridgeSupport672_suffix_009
def ridgeSupport672_suffix_007 : List Nat := ridgeSupport672_007 ++ ridgeSupport672_suffix_008
def ridgeSupport672_suffix_006 : List Nat := ridgeSupport672_006 ++ ridgeSupport672_suffix_007
def ridgeSupport672_suffix_005 : List Nat := ridgeSupport672_005 ++ ridgeSupport672_suffix_006
def ridgeSupport672_suffix_004 : List Nat := ridgeSupport672_004 ++ ridgeSupport672_suffix_005
def ridgeSupport672_suffix_003 : List Nat := ridgeSupport672_003 ++ ridgeSupport672_suffix_004
def ridgeSupport672_suffix_002 : List Nat := ridgeSupport672_002 ++ ridgeSupport672_suffix_003
def ridgeSupport672_suffix_001 : List Nat := ridgeSupport672_001 ++ ridgeSupport672_suffix_002
def ridgeSupport672_suffix_000 : List Nat := ridgeSupport672_000 ++ ridgeSupport672_suffix_001
theorem ridgeSupport672_source : candidateSupports 672 =
    (PackedRawNatGrowth.readList 13 378 ridgeSupport672_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
