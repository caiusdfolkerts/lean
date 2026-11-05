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
def ridgeSupport280_000 : List Nat := [69,72,74,76,332,1001,1003,1006,1007,1009,1025,1027,1030,1031,1033,1050,1052,1053,1056,1058,1061,1062,1064,1065,1068,1069,1070,1072,1073,1075,1080,1081]
def ridgeSupport280_001 : List Nat := [1103,1105,1106,1108,1109,1111,1113,1114,1116,1117,1120,1121,1124,1126,1127,1129,1130,1132,1134,1135,1137,1138,1141,1142,3406,3407,3412,3413,3416,3417,3418,3419]
def ridgeSupport280_002 : List Nat := [3420,3421,3426,3427,3430,3431,3436,3437,3440,3441,3442,3443,3444,3445,3450,3451,3464,3465,3466,3467,3468,3469,3488,3489,3490,3491,3492,3493,3512,3513,3514,3515]
def ridgeSupport280_003 : List Nat := [3516,3517,3536,3537,3538,3539,3540,3541,3560,3561,3562,3563,3564,3565,3584,3585,3586,3587,3588,3589,3597,3600,3603,3606,3608,3609,3610,3611,3612,3613,3614,3616]
def ridgeSupport280_004 : List Nat := [3660,3664,3669,3671,3673,3675,3692,3696,3701,3703,3705,3707,3725,3729,3732,3734,3736,3738,4848,4849,4860,4861,4884,4885,4896,4897,4904,4906,4910,4912,4990,4991]
def ridgeSupport280_005 : List Nat := [5002,5003,5026,5027,5038,5039,5049,5052,5055,5058,5062,5063,5074,5075,5098,5099,5110,5111,5121,5124,5127,5130,6358,6359,6362,6363,6366,6367,6370,6371,6374,6375]
def ridgeSupport280_006 : List Nat := [6378,6379,6392,6393,6394,6395,6396,6397,6416,6417,6418,6419,6420,6421,6429,6432,6435,6438,6440,6441,6442,6443,6444,6445,6446,6448,6453,6456,6459,6462,6464,6465]
def ridgeSupport280_007 : List Nat := [6466,6467,6468,6469,6470,6472,6476,6478,6479,6481,6486,6487,6492,6494,6500,6502,6509,6511,7152,7153,7164,7165,7172,7174,7178,7180,7188,7189,7191,7193,7200,7201]
def ridgeSupport280_008 : List Nat := [7258,7259,7270,7271,7281,7284,7287,7290,7294,7295,7298,7303,7306,7307,7312,7313,7324,7325,7335,7338,7341,7344,7348,7349,7352,7357,7360,7361,7486,7487,7490,7491]
def ridgeSupport280_009 : List Nat := [7494,7495,7560,7561,7570,7571,7576,7577,7856,7857,7858,7859,7860,7861,7884,7892,7901]
def ridgeSupport280_code : Nat := 0x1eddf6a7b33d6beb4f59facbd63eb0eccf663b27d92ec4f623a8fd46ea1f50ba7fd3ee60f30397bcb8e5af2d3961cade55729f93bc9ce48f243917c8ae43f20b8ffc7ee3d71df8e9c71e33f19b8b7c5ae10f083833c17e0af053819c0ae0370137fbbfcdf8efc32df96dcb365932bd95ccabe55b2a394fca76533291946ca2e513287942ca0e50327d93bc9c64d726192ec96e4b325792ac94e4a324d923c90647722b914c89e44b223910c7ee3f31f78fac7ce3e31d78eac73e39b1c78e2c6fe37b1b78dac6be35a815407a0250067ef3f69f5cfaa7a73d29e3cf1a7853bf9de4ee675f3ae9d1ce8a71738a9bfcdfa66132e9954ca264332098acc525fb2fc978cbc1d34e9874b3a51d22e8d73db9e5ceee7573839b1cb6e5972bb955ca0e4c7103879c3ae1c70db869c32e1870b384dc20e0d702b811c06e02700b801bdadec6f5b7a9bd2de86eab751ba6dd26e8b741b7adbc6ddb6e9b72db86d2b691b46da26d0b681b1ad8c6c5b629b12d886bdb5e9aead746b9b5c9ae2d706b6b5b1aced666b1b589abad5c6adb569ab2d586aab551a9ed4e23b11d48e447123791b88d846a234919c8cc46423091808ba45c22d11648ae45522a11488a244f21c90e086643121810b885a42c21490a084c425211108083a41c20d102480e40620190047e23ef1f70fac7d214c0260128090045
def ridgeSupport280_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport280_code
def ridgeSupport280_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport280_code
def ridgeSupport280_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport280_code
def ridgeSupport280_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport280_code
def ridgeSupport280_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport280_code
def ridgeSupport280_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport280_code
def ridgeSupport280_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport280_code
def ridgeSupport280_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport280_code
def ridgeSupport280_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport280_code
def ridgeSupport280_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport280_code
def ridgeSupport280_rest_010 : Nat := PackedRawNatGrowth.drop 3965 ridgeSupport280_code
def ridgeSupport280_suffix_010 : List Nat := []
def ridgeSupport280_suffix_009 : List Nat := ridgeSupport280_009 ++ ridgeSupport280_suffix_010
def ridgeSupport280_suffix_008 : List Nat := ridgeSupport280_008 ++ ridgeSupport280_suffix_009
def ridgeSupport280_suffix_007 : List Nat := ridgeSupport280_007 ++ ridgeSupport280_suffix_008
def ridgeSupport280_suffix_006 : List Nat := ridgeSupport280_006 ++ ridgeSupport280_suffix_007
def ridgeSupport280_suffix_005 : List Nat := ridgeSupport280_005 ++ ridgeSupport280_suffix_006
def ridgeSupport280_suffix_004 : List Nat := ridgeSupport280_004 ++ ridgeSupport280_suffix_005
def ridgeSupport280_suffix_003 : List Nat := ridgeSupport280_003 ++ ridgeSupport280_suffix_004
def ridgeSupport280_suffix_002 : List Nat := ridgeSupport280_002 ++ ridgeSupport280_suffix_003
def ridgeSupport280_suffix_001 : List Nat := ridgeSupport280_001 ++ ridgeSupport280_suffix_002
def ridgeSupport280_suffix_000 : List Nat := ridgeSupport280_000 ++ ridgeSupport280_suffix_001
theorem ridgeSupport280_source : candidateSupports 280 =
    (PackedRawNatGrowth.readList 13 305 ridgeSupport280_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase02
