module
prelude
public import RootedSixBase02GrowthCacheData
public import PackedListAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
def ridgeSupport152_000 : List Nat := [68,71,74,75,331,989,991,994,995,997,1026,1028,1029,1032,1034,1038,1040,1041,1044,1046,1061,1063,1064,1066,1067,1069,1071,1072,1074,1075,1078,1079]
def ridgeSupport152_001 : List Nat := [1082,1084,1085,1087,1088,1090,1092,1093,1095,1096,1099,1100,1125,1126,1128,1129,1130,1131,1133,1134,1136,1137,1139,1140,3404,3405,3410,3411,3412,3413,3414,3415]
def ridgeSupport152_002 : List Nat := [3418,3419,3424,3425,3428,3429,3434,3435,3436,3437,3438,3439,3442,3443,3448,3449,3458,3459,3460,3461,3462,3463,3482,3483,3484,3485,3486,3487,3506,3507,3508,3509]
def ridgeSupport152_003 : List Nat := [3510,3511,3530,3531,3532,3533,3534,3535,3554,3555,3556,3557,3558,3559,3578,3579,3580,3581,3582,3583,3599,3601,3602,3603,3604,3605,3606,3607,3609,3612,3615,3618]
def ridgeSupport152_004 : List Nat := [3644,3648,3653,3655,3657,3659,3693,3697,3700,3702,3704,3706,3709,3713,3716,3718,3720,3722,4846,4847,4858,4859,4882,4883,4894,4895,4905,4908,4911,4914,4918,4919]
def ridgeSupport152_005 : List Nat := [4930,4931,4954,4955,4966,4967,4977,4980,4983,4986,5060,5061,5072,5073,5096,5097,5108,5109,5123,5125,5129,5131,6356,6357,6362,6363,6364,6365,6368,6369,6374,6375]
def ridgeSupport152_006 : List Nat := [6376,6377,6386,6387,6388,6389,6390,6391,6410,6411,6412,6413,6414,6415,6431,6433,6434,6435,6436,6437,6438,6439,6441,6444,6447,6450,6455,6457,6458,6459,6460,6461]
def ridgeSupport152_007 : List Nat := [6462,6463,6465,6468,6471,6474,6476,6477,6482,6484,6485,6487,6488,6490,6501,6503,6505,6507,7150,7151,7162,7163,7173,7176,7179,7182,7186,7187,7190,7195,7198,7199]
def ridgeSupport152_008 : List Nat := [7204,7205,7216,7217,7227,7230,7233,7236,7240,7241,7244,7249,7252,7253,7310,7311,7322,7323,7337,7339,7343,7345,7346,7347,7354,7356,7358,7359,7484,7485,7490,7491]
def ridgeSupport152_009 : List Nat := [7492,7493,7558,7559,7564,7565,7574,7575,7850,7851,7852,7853,7854,7855,7880,7893,7897]
def ridgeSupport152_code : Nat := 0x1ed9f6afb23d5feaef56fab3d57eaaecbf65bb1bd8cec3f61ba8bd44ea1f50ba7bd3ce5ff2fb979cbae59f2cb963cafe55f2a7937c9ae47f23b8abc54e28f133893c48e22710787dc3be18f0c384bc24e0ff07b837c16e09f04b81dc0be0470177f7bfadf7efbb2d7969cb3e5972b5958cabe5572a9952ca6e533295947ca2650727f93ec9ee4f327793ac9ce4df26592fc9664a724f926c92e493247922c90e47f21f90ec86e43321790ac7be3db1eb8f4c79e3cb1d38e8c73e39b1c38e0c6ee3731b78dac6ae352817409a02d00e7eb3f49f4cfa27a33d09e2cf126f53779ba4dc66cf3669adcd6a68734299bccda66532f9964ca663f31e989cc4a5f72fa977cbb9d14e887433a11d02e7d73d39e1cece74738b9b5c96e49723b915c80e3c711387dc38e1970bb859c2ae14709b849c22e0f6ffb7f9bfadfc6fdb7e9bcede66f2b791bc6de26e7b739b9adcc6e5b729b6edb66dab6d1b66db26cfb679b3ad9c6cdb669b0ed866c2b611b06d826bcb5e1ae6d726b7b5b9adad6c6b5b5a9acad646b0b581ab6d5a6abb559aaad546a9b549a9ad4c23a11cc8e247023711b48d646a23491a08cc465226112c890447222911088444021f90f487843a21b90d886643221810bc85a42b21510a084e42520b1050822410207102881040520210087ca3e31f10f7c7ba14b025812808e044
def ridgeSupport152_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport152_code
def ridgeSupport152_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport152_code
def ridgeSupport152_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport152_code
def ridgeSupport152_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport152_code
def ridgeSupport152_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport152_code
def ridgeSupport152_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport152_code
def ridgeSupport152_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport152_code
def ridgeSupport152_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport152_code
def ridgeSupport152_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport152_code
def ridgeSupport152_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport152_code
def ridgeSupport152_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport152_code
def ridgeSupport152_suffix_010 : List Nat := []
def ridgeSupport152_suffix_009 : List Nat := ridgeSupport152_009 ++ ridgeSupport152_suffix_010
def ridgeSupport152_suffix_008 : List Nat := ridgeSupport152_008 ++ ridgeSupport152_suffix_009
def ridgeSupport152_suffix_007 : List Nat := ridgeSupport152_007 ++ ridgeSupport152_suffix_008
def ridgeSupport152_suffix_006 : List Nat := ridgeSupport152_006 ++ ridgeSupport152_suffix_007
def ridgeSupport152_suffix_005 : List Nat := ridgeSupport152_005 ++ ridgeSupport152_suffix_006
def ridgeSupport152_suffix_004 : List Nat := ridgeSupport152_004 ++ ridgeSupport152_suffix_005
def ridgeSupport152_suffix_003 : List Nat := ridgeSupport152_003 ++ ridgeSupport152_suffix_004
def ridgeSupport152_suffix_002 : List Nat := ridgeSupport152_002 ++ ridgeSupport152_suffix_003
def ridgeSupport152_suffix_001 : List Nat := ridgeSupport152_001 ++ ridgeSupport152_suffix_002
def ridgeSupport152_suffix_000 : List Nat := ridgeSupport152_000 ++ ridgeSupport152_suffix_001
theorem ridgeSupport152_source : candidateSupports 152 =
    (PackedRawNatGrowth.readList 13 305 ridgeSupport152_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
