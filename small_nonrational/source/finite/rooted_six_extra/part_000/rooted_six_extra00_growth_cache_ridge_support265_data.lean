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
def ridgeSupport265_000 : List Nat := [7,17,26,28,30,214,217,218,221,224,238,241,242,245,248,263,264,267,268,273,370,373,374,377,380,394,397,398,401,404,419,420]
def ridgeSupport265_001 : List Nat := [423,424,429,514,515,517,518,521,522,523,525,526,528,533,534,556,558,559,561,562,564,566,567,569,570,573,574,577,579,580,582,583]
def ridgeSupport265_002 : List Nat := [585,587,588,590,591,594,595,2874,2875,2880,2881,2884,2885,2886,2887,2888,2889,2894,2895,2898,2899,2904,2905,2908,2909,2910,2911,2912,2913,2918,2919,2932]
def ridgeSupport265_003 : List Nat := [2933,2934,2935,2936,2937,2956,2957,2958,2959,2960,2961,2980,2981,2982,2983,2984,2985,3004,3005,3006,3007,3008,3009,3028,3029,3030,3031,3032,3033,3052,3053,3054]
def ridgeSupport265_004 : List Nat := [3055,3056,3057,3065,3068,3071,3074,3076,3077,3078,3079,3080,3081,3082,3084,3362,3363,3380,3381,3398,3399,3400,3402,3406,3408,3416,3417,3504,3505,3522,3523,3540]
def ridgeSupport265_005 : List Nat := [3541,3545,3548,3551,3554,3558,3559,3576,3577,3594,3595,3612,3613,3617,3620,3623,3626,3630,3631,3890,3891,3908,3909,3926,3927,3928,3930,3934,3936,3944,3945,4032]
def ridgeSupport265_006 : List Nat := [4033,4050,4051,4068,4069,4073,4076,4079,4082,4086,4087,4104,4105,4122,4123,4140,4141,4145,4148,4151,4154,4158,4159,7192,7193,7194,7195,7196,7197,7900,7901,7902]
def ridgeSupport265_007 : List Nat := [7903,7904,7905,7913,7916,7919,7921,7922,7923,7925,7928,7931,7933,7934,7935,7984,7986,8000,8001,8021,8024,8034,8035,8039,8042,8052,8053,8104,8106,8120,8121,8141]
def ridgeSupport265_008 : List Nat := [8144,8154,8155,8159,8162,8172,8173]
def ridgeSupport265_code : Nat := 0x1fed7fb1fe27f7dfdb7f69fd07f35fb97ee1faa7ea1f757dd1f6a7d9df637d89f587d55f417d01f327cc1eff7bf9efd7bedef87bd5ef37bc9ef17bbdeec7ba5ee17b81edf7b79edd7b71c1d7071c1b7069c19706103f40f903a40dd03440c502d40b101b40690094020ff73fd8ff23fbcfec3fa4fe53f90fd33f48fc13f00f693da0f603d78f5a3d60f573d58f453d10f333cc8e2f38b8e2a389ce243884e1d3870e0b3828df937e0de73798de2377cddc3764dd53750dc33708db136c0d593560d503538d4a3520d473518d3534d0d233488c0c3028c093020c073018c053010c022ffcbfc2fe4bf12fc0bef2fb8bed2fb0bd92f60bd72f58bd52f50bc12f00bbf2ef8bbd2ef0ba92ea0ba72e98ba52e90b912e40b8f2e38b8d2e30b792de0b772dd8b752dd0b672d98b612d80b5f2d78b5d2d70b592d60b532d48b4f2d38b492d20b472d18b452d10b412d00b3b2ce8253094824f093824c092c249091c2460910243090423e08f423a08e423708d823408c823108bc22e08b02160854210083820d082c20a0824206081420308081ad06a01a706901a30650191063818d062817c05e417605d4172044410c042c108041c0f803d40f203c40ee03800dd03680d9035801e007001a0044007
def ridgeSupport265_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport265_code
def ridgeSupport265_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport265_code
def ridgeSupport265_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport265_code
def ridgeSupport265_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport265_code
def ridgeSupport265_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport265_code
def ridgeSupport265_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport265_code
def ridgeSupport265_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport265_code
def ridgeSupport265_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport265_code
def ridgeSupport265_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport265_code
def ridgeSupport265_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport265_code
def ridgeSupport265_suffix_009 : List Nat := []
def ridgeSupport265_suffix_008 : List Nat := ridgeSupport265_008 ++ ridgeSupport265_suffix_009
def ridgeSupport265_suffix_007 : List Nat := ridgeSupport265_007 ++ ridgeSupport265_suffix_008
def ridgeSupport265_suffix_006 : List Nat := ridgeSupport265_006 ++ ridgeSupport265_suffix_007
def ridgeSupport265_suffix_005 : List Nat := ridgeSupport265_005 ++ ridgeSupport265_suffix_006
def ridgeSupport265_suffix_004 : List Nat := ridgeSupport265_004 ++ ridgeSupport265_suffix_005
def ridgeSupport265_suffix_003 : List Nat := ridgeSupport265_003 ++ ridgeSupport265_suffix_004
def ridgeSupport265_suffix_002 : List Nat := ridgeSupport265_002 ++ ridgeSupport265_suffix_003
def ridgeSupport265_suffix_001 : List Nat := ridgeSupport265_001 ++ ridgeSupport265_suffix_002
def ridgeSupport265_suffix_000 : List Nat := ridgeSupport265_000 ++ ridgeSupport265_suffix_001
theorem ridgeSupport265_source : candidateSupports 265 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport265_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
