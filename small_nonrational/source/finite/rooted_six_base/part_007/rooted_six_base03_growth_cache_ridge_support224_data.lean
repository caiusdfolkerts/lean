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
def ridgeSupport224_000 : List Nat := [51,71,91,101,111,112,541,542,543,544,551,552,697,698,699,700,707,708,853,854,858,860,861,865,867,868,870,874,875,879,881,882]
def ridgeSupport224_001 : List Nat := [886,888,889,891,962,963,964,965,972,973,1118,1119,1123,1125,1126,1130,1132,1133,1135,1139,1140,1144,1146,1147,1151,1153,1154,1156,1227,1228,1229,1230]
def ridgeSupport224_002 : List Nat := [1237,1238,1383,1384,1388,1390,1391,1395,1397,1398,1400,1404,1405,1409,1411,1412,1416,1418,1419,1421,1492,1493,1497,1499,1500,1504,1506,1507,1509,1513,1514,1518]
def ridgeSupport224_003 : List Nat := [1520,1521,1525,1527,1528,1530,1603,1604,1606,1607,1608,1609,1611,1612,1614,1615,1617,1618,3009,3011,3013,3015,3033,3035,3039,3041,3046,3047,3052,3053,3054,3055]
def ridgeSupport224_004 : List Nat := [3060,3061,3094,3095,3100,3101,3102,3103,3108,3109,3115,3117,3121,3123,3133,3134,3136,3137,3141,3143,3145,3147,3165,3167,3171,3173,3178,3179,3184,3185,3186,3187]
def ridgeSupport224_005 : List Nat := [3192,3193,3226,3227,3232,3233,3234,3235,3240,3241,3247,3249,3253,3255,3265,3266,3268,3269,3274,3275,3277,3279,3286,3287,3289,3291,3310,3311,3322,3323,3328,3329]
def ridgeSupport224_006 : List Nat := [3331,3333,3340,3341,3343,3345,3364,3365,3376,3377,3489,3491,3493,3495,3513,3515,3519,3521,3526,3527,3532,3533,3534,3535,3540,3541,3574,3575,3580,3581,3582,3583]
def ridgeSupport224_007 : List Nat := [3588,3589,3595,3597,3601,3603,3613,3614,3616,3617,3622,3623,3625,3627,3634,3635,3637,3639,3658,3659,3670,3671,3676,3677,3679,3681,3688,3689,3691,3693,3712,3713]
def ridgeSupport224_008 : List Nat := [3724,3725,3837,3839,3841,3843,3861,3863,3867,3869,3874,3875,3880,3881,3882,3883,3888,3889,3922,3923,3928,3929,3930,3931,3936,3937,3943,3945,3949,3951,3961,3962]
def ridgeSupport224_009 : List Nat := [3964,3965,3970,3971,3973,3975,3982,3983,3985,3987,4006,4007,4018,4019,4024,4025,4027,4029,4036,4037,4039,4041,4060,4061,4072,4073,4186,4187,4189,4191,4198,4199]
def ridgeSupport224_010 : List Nat := [4201,4203,4222,4223,4234,4235,4240,4241,4243,4245,4252,4253,4255,4257,4276,4277,4288,4289,4533,4535,4537,4539,4545,4547,4549,4551,4558,4559,4564,4565,4581,4583]
def ridgeSupport224_011 : List Nat := [4585,4587,4594,4595,4600,4601,4617,4619,4621,4623,4630,4631,4636,4637,4654,4655,4660,4661,5032,5033,5068,5069,5128,5129,5188,5189]
def ridgeSupport224_code : Nat := 0x288b444a04d02279b3cc9d4cea246b234917c8ba43b21c90bc85a41f20d905c8263f31f88f9c7ca3d71e98f3c7963ab1d48e7c73a38f1c58e1c7063771b98dbc6d61830c085ac2d214309f84ec27212b093848c24211708a83fc1fa0d7069833c19a0bf05d82dc169fd2fe87eebf71f92fc77e2bf11f7afbb7dcbee1f66fb27d3be99f26f917c7be39f0ef857c1be09efaf7c7bd3de5edef6d7b4bd9dec2f607adbd69eb2f587a9bd49e62f30795bca9e52f28791bc89e3af1b78bbc55e06f0177fbbf5d1ae8c740ba01cdae6b734b9a1cc2e5f72eb971caee56725b929c6ee35719b8c9c56e29713b899c42e2070f3875c26e11706b82dc0ae046ffb7f9bfadfc6fbb7d9baadd46e7b739b9adcc6e3b719b82dbf6ddb6e5b4eda56d1b685a62d30692b491a22d0f686b431a0ad03680b4019f6cfa677b3b99b6cd966bb35999eccd665b32998acc4661330596ecb5658b2bd952ca8651b289942ca064db2698f2c78639b1c98e2c70635b1a98cac6362fb175896c49623b115882c4061f30f5866c31616b0ad84ac2460fb07983ac1c60bb0597eabf45f7afb97dabec5f3af997c2bdf5edaf6578ebc55e1af04ca46513279938c9864b3249920c8e646322190cbf45f82fb97d4be25f02f717a8bd25e52f19788bc05dc2ed9764baa5d42c6962cb145882c2160cb0257d2be15e0aec5752b995bcadc56c2b4159c9ac4d526713349984cb242120890247f23d91e88f047423991bc8da46c23511988ca46322f917879a3cc1e28f107863c21bd8de46f03761b90dc46de36b1b50d986c83631b08d746b835a1ab0d545882c315e0aec5742b9114089c44021f10f08740e006f032816c08e033
def ridgeSupport224_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport224_code
def ridgeSupport224_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport224_code
def ridgeSupport224_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport224_code
def ridgeSupport224_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport224_code
def ridgeSupport224_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport224_code
def ridgeSupport224_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport224_code
def ridgeSupport224_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport224_code
def ridgeSupport224_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport224_code
def ridgeSupport224_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport224_code
def ridgeSupport224_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport224_code
def ridgeSupport224_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport224_code
def ridgeSupport224_rest_011 : Nat := PackedRawNatGrowth.drop 4576 ridgeSupport224_code
def ridgeSupport224_rest_012 : Nat := PackedRawNatGrowth.drop 4914 ridgeSupport224_code
def ridgeSupport224_suffix_012 : List Nat := []
def ridgeSupport224_suffix_011 : List Nat := ridgeSupport224_011 ++ ridgeSupport224_suffix_012
def ridgeSupport224_suffix_010 : List Nat := ridgeSupport224_010 ++ ridgeSupport224_suffix_011
def ridgeSupport224_suffix_009 : List Nat := ridgeSupport224_009 ++ ridgeSupport224_suffix_010
def ridgeSupport224_suffix_008 : List Nat := ridgeSupport224_008 ++ ridgeSupport224_suffix_009
def ridgeSupport224_suffix_007 : List Nat := ridgeSupport224_007 ++ ridgeSupport224_suffix_008
def ridgeSupport224_suffix_006 : List Nat := ridgeSupport224_006 ++ ridgeSupport224_suffix_007
def ridgeSupport224_suffix_005 : List Nat := ridgeSupport224_005 ++ ridgeSupport224_suffix_006
def ridgeSupport224_suffix_004 : List Nat := ridgeSupport224_004 ++ ridgeSupport224_suffix_005
def ridgeSupport224_suffix_003 : List Nat := ridgeSupport224_003 ++ ridgeSupport224_suffix_004
def ridgeSupport224_suffix_002 : List Nat := ridgeSupport224_002 ++ ridgeSupport224_suffix_003
def ridgeSupport224_suffix_001 : List Nat := ridgeSupport224_001 ++ ridgeSupport224_suffix_002
def ridgeSupport224_suffix_000 : List Nat := ridgeSupport224_000 ++ ridgeSupport224_suffix_001
theorem ridgeSupport224_source : candidateSupports 224 =
    (PackedRawNatGrowth.readList 13 378 ridgeSupport224_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
