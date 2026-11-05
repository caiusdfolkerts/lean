module
prelude
public import RootedSixExtra00GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport11_000 : List Nat := [0,5,6,7,8,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228]
def ridgeSupport11_001 : List Nat := [229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255,256,257,258,259,260]
def ridgeSupport11_002 : List Nat := [261,262,263,264,265,266,267,268,269,270,271,272,273,3352,3353,3354,3355,3356,3357,3358,3359,3360,3361,3362,3363,3364,3365,3366,3367,3368,3369,3370]
def ridgeSupport11_003 : List Nat := [3371,3372,3373,3374,3375,3376,3377,3378,3379,3380,3381,3382,3383,3384,3385,3386,3387,3388,3389,3390,3391,3392,3393,3394,3395,3396,3397,3398,3399,3400,3401,3402]
def ridgeSupport11_004 : List Nat := [3403,3404,3405,3406,3407,3408,3409,3410,3411,3412,3413,3414,3415,3416,3417,3418,3419,3420,3421,3422,3423,3424,3425,3426,3427,3428,3429,3430,3431,3432,3433,3434]
def ridgeSupport11_005 : List Nat := [3435,3436,3437,3438,3439,3440,3441,3442,3443,3444,3445,3446,3447,3448,3449,3450,3451,3452,3453,3454,3455,3456,3457,3458,3459,3460,3461,3462,3463,3464,3465,3466]
def ridgeSupport11_006 : List Nat := [3467,3468,3469,3470,3471,3472,3473,3474,3475,3476,3477,3478,3479,3480,3481,3482,3483,3484,3485,3486,3487,3488,3489,3490,3491,3492,3493,3494,3495,3496,3497,3498]
def ridgeSupport11_007 : List Nat := [3499,3500,3501,3502,3503,3504,3505,3506,3507,3508,3509,3510,3511,3512,3513,3514,3515,3516,3517,3518,3519,3520,3521,3522,3523,3524,3525,3526,3527,3528,3529,3530]
def ridgeSupport11_008 : List Nat := [3531,3532,3533,3534,3535,3536,3537,3538,3539,3540,3541,3542,3543,3544,3545,3546,3547,3548,3549,3550,3551,3552,3553,3554,3555,3556,3557,3558,3559,3560,3561,3562]
def ridgeSupport11_009 : List Nat := [3563,3564,3565,3566,3567,3568,3569,3570,3571,3572,3573,3574,3575,3576,3577,3578,3579,3580,3581,3582,3583,3584,3585,3586,3587,3588,3589,3590,3591,3592,3593,3594]
def ridgeSupport11_010 : List Nat := [3595,3596,3597,3598,3599,3600,3601,3602,3603,3604,3605,3606,3607,3608,3609,3610,3611,3612,3613,3614,3615,3616,3617,3618,3619,3620,3621,3622,3623,3624,3625,3626]
def ridgeSupport11_011 : List Nat := [3627,3628,3629,3630,3631,3632,3633,3634,3635,3636,3637,3638,3639,7252,7253,7254,7255,7256,7257,7258,7259,7260,7261,7262,7263,7264,7265,7266,7267,7268,7269,7270]
def ridgeSupport11_012 : List Nat := [7271,7272,7273,7274,7275,7984,7985,7986,7987,7988,7989,7990,7991,7992,7993,7994,7995,7996,7997,7998,7999,8000,8001,8002,8003,8004,8005,8006,8007,8008,8009,8010]
def ridgeSupport11_013 : List Nat := [8011,8012,8013,8014,8015,8016,8017,8018,8019,8020,8021,8022,8023,8024,8025,8026,8027,8028,8029,8030,8031,8032,8033,8034,8035,8036,8037,8038,8039,8040,8041,8042]
def ridgeSupport11_014 : List Nat := [8043,8044,8045,8046,8047,8048,8049,8050,8051,8052,8053,8054,8055]
def ridgeSupport11_code : Nat := 0x1f777dd9f757dd1f737dc9f717dc1f6f7db9f6d7db1f6b7da9f697da1f677d99f657d91f637d89f617d81f5f7d79f5d7d71f5b7d69f597d61f577d59f557d51f537d49f517d41f4f7d39f4d7d31f4b7d29f497d21f477d19f457d11f437d09f417d01f3f7cf9f3d7cf1f3b7ce9f397ce1f377cd9f357cd1f337cc9f317cc1c6b71a9c6971a1c677199c657191c637189c617181c5f7179c5d7171c5b7169c597161c577159c557150e3738d8e3538d0e3338c8e3138c0e2f38b8e2d38b0e2b38a8e2938a0e273898e253890e233888e213880e1f3878e1d3870e1b3868e193860e173858e153850e133848e113840e0f3838e0d3830e0b3828e093820e073818e053810e033808e013800dff37f8dfd37f0dfb37e8df937e0df737d8df537d0df337c8df137c0def37b8ded37b0deb37a8de937a0de73798de53790de33788de13780ddf3778ddd3770ddb3768dd93760dd73758dd53750dd33748dd13740dcf3738dcd3730dcb3728dc93720dc73718dc53710dc33708dc13700dbf36f8dbd36f0dbb36e8db936e0db736d8db536d0db336c8db136c0daf36b8dad36b0dab36a8da936a0da73698da53690da33688da13680d9f3678d9d3670d9b3668d993660d973658d953650d933648d913640d8f3638d8d3630d8b3628d893620d873618d853610d833608d813600d7f35f8d7d35f0d7b35e8d7935e0d7735d8d7535d0d7335c8d7135c0d6f35b8d6d35b0d6b35a8d6935a0d673598d653590d633588d613580d5f3578d5d3570d5b3568d593560d573558d553550d533548d513540d4f3538d4d3530d4b3528d493520d473518d453510d433508d413500d3f34f8d3d34f0d3b34e8d3934e0d3734d8d3534d0d3334c8d3134c0d2f34b8d2d34b0d2b34a8d2934a0d273498d253490d233488d213480d1f3478d1d3470d1b3468d193460111044010f043810d043010b0428109042010704181050410103040810104000ff03f80fd03f00fb03e80f903e00f703d80f503d00f303c80f103c00ef03b80ed03b00eb03a80e903a00e703980e503900e303880e103800df03780dd03700db03680d903600d703580d503500d303480d103400cf03380cd03300cb0328008001c0060014000
def ridgeSupport11_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport11_code
def ridgeSupport11_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport11_code
def ridgeSupport11_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport11_code
def ridgeSupport11_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport11_code
def ridgeSupport11_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport11_code
def ridgeSupport11_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport11_code
def ridgeSupport11_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport11_code
def ridgeSupport11_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport11_code
def ridgeSupport11_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport11_code
def ridgeSupport11_rest_009 : Nat := PackedRawNatGrowth.drop 4032 ridgeSupport11_code
def ridgeSupport11_rest_010 : Nat := PackedRawNatGrowth.drop 4480 ridgeSupport11_code
def ridgeSupport11_rest_011 : Nat := PackedRawNatGrowth.drop 4928 ridgeSupport11_code
def ridgeSupport11_rest_012 : Nat := PackedRawNatGrowth.drop 5376 ridgeSupport11_code
def ridgeSupport11_rest_013 : Nat := PackedRawNatGrowth.drop 5824 ridgeSupport11_code
def ridgeSupport11_rest_014 : Nat := PackedRawNatGrowth.drop 6272 ridgeSupport11_code
def ridgeSupport11_rest_015 : Nat := PackedRawNatGrowth.drop 6454 ridgeSupport11_code
def ridgeSupport11_suffix_015 : List Nat := []
def ridgeSupport11_suffix_014 : List Nat := ridgeSupport11_014 ++ ridgeSupport11_suffix_015
def ridgeSupport11_suffix_013 : List Nat := ridgeSupport11_013 ++ ridgeSupport11_suffix_014
def ridgeSupport11_suffix_012 : List Nat := ridgeSupport11_012 ++ ridgeSupport11_suffix_013
def ridgeSupport11_suffix_011 : List Nat := ridgeSupport11_011 ++ ridgeSupport11_suffix_012
def ridgeSupport11_suffix_010 : List Nat := ridgeSupport11_010 ++ ridgeSupport11_suffix_011
def ridgeSupport11_suffix_009 : List Nat := ridgeSupport11_009 ++ ridgeSupport11_suffix_010
def ridgeSupport11_suffix_008 : List Nat := ridgeSupport11_008 ++ ridgeSupport11_suffix_009
def ridgeSupport11_suffix_007 : List Nat := ridgeSupport11_007 ++ ridgeSupport11_suffix_008
def ridgeSupport11_suffix_006 : List Nat := ridgeSupport11_006 ++ ridgeSupport11_suffix_007
def ridgeSupport11_suffix_005 : List Nat := ridgeSupport11_005 ++ ridgeSupport11_suffix_006
def ridgeSupport11_suffix_004 : List Nat := ridgeSupport11_004 ++ ridgeSupport11_suffix_005
def ridgeSupport11_suffix_003 : List Nat := ridgeSupport11_003 ++ ridgeSupport11_suffix_004
def ridgeSupport11_suffix_002 : List Nat := ridgeSupport11_002 ++ ridgeSupport11_suffix_003
def ridgeSupport11_suffix_001 : List Nat := ridgeSupport11_001 ++ ridgeSupport11_suffix_002
def ridgeSupport11_suffix_000 : List Nat := ridgeSupport11_000 ++ ridgeSupport11_suffix_001
theorem ridgeSupport11_source : candidateSupports 11 =
    (PackedRawNatGrowth.readList 14 461 ridgeSupport11_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
