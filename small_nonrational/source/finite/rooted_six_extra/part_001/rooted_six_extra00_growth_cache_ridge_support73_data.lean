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
def ridgeSupport73_000 : List Nat := [5,15,25,26,27,203,204,207,208,213,215,216,219,220,225,227,228,231,232,237,359,360,363,364,369,371,372,375,376,381,383,384]
def ridgeSupport73_001 : List Nat := [387,388,393,515,516,518,519,520,521,523,524,526,527,529,530,536,537,539,540,541,542,544,545,547,548,550,551,557,558,560,561,562]
def ridgeSupport73_002 : List Nat := [563,565,566,568,569,571,572,2872,2873,2874,2875,2876,2877,2878,2879,2884,2885,2890,2891,2896,2897,2898,2899,2900,2901,2902,2903,2908,2909,2914,2915,2920]
def ridgeSupport73_003 : List Nat := [2921,2922,2923,2924,2925,2944,2945,2946,2947,2948,2949,2968,2969,2970,2971,2972,2973,2992,2993,2994,2995,2996,2997,3016,3017,3018,3019,3020,3021,3040,3041,3042]
def ridgeSupport73_004 : List Nat := [3043,3044,3045,3064,3065,3066,3067,3068,3069,3073,3075,3079,3081,3085,3087,3358,3359,3376,3377,3394,3395,3403,3405,3409,3411,3412,3413,3430,3431,3448,3449,3466]
def ridgeSupport73_005 : List Nat := [3467,3475,3477,3481,3483,3484,3485,3502,3503,3520,3521,3538,3539,3547,3549,3553,3555,3556,3557,3886,3887,3904,3905,3922,3923,3931,3933,3937,3939,3940,3941,3958]
def ridgeSupport73_006 : List Nat := [3959,3976,3977,3994,3995,4003,4005,4009,4011,4012,4013,4030,4031,4048,4049,4066,4067,4075,4077,4081,4083,4084,4085,7180,7181,7182,7183,7184,7185,7888,7889,7890]
def ridgeSupport73_007 : List Nat := [7891,7892,7893,7912,7913,7914,7915,7916,7917,7924,7925,7926,7927,7928,7929,7987,7989,7996,7997,8005,8007,8014,8015,8023,8025,8032,8033,8107,8109,8116,8117,8125]
def ridgeSupport73_008 : List Nat := [8127,8134,8135,8143,8145,8152,8153]
def ridgeSupport73_code : Nat := 0x1fd97f61fd17f3dfc77f19fbf7ef5fb57ed1fad7eadf617d81f597d5df4f7d39f477d15f3d7cf1f357ccdef97be1ef77bd9ef57bd1eed7bb1eeb7ba9ee97ba1ed57b51ed37b49ed17b41c117041c0f7039c0d7030ff53fd0ff33fc4fed3facfe33f88fd13f40fbf3ef8fad3eb0fab3ea4fa53e8cf9b3e68f893e20f773dd8f653d90f633d84f5d3d6cf533d48f413d00f2f3cb8de53790de33784ddd376cdd33748dc13700daf36b8d9d3670d9b3664d95364cd8b3628d7935e0d673598d553550d533544d4d352cd433508d3134c0d1f3478c0f3034c09301cc033004bfd2ff0bfb2fe8bf92fe0be52f90be32f88be12f80bcd2f30bcb2f28bc92f20bb52ed0bb32ec8bb12ec0b9d2e70b9b2e68b992e60b852e10b832e08b812e00b6d2db0b6b2da8b692da0b632d88b5d2d70b572d58b552d50b532d48b512d40b4b2d28b452d10b3f2cf8b3d2cf0b3b2ce8b392ce023c08ec23908e023608d423308c823108c022e08b42270898224088c221088021e087421c086c2190860212084420f083820c082c20908202070818204080c1890610183060017f05f417805dc17405cc17105b016b05a016703b40e8039c0e4038c0e103700db03600d703540d0033c0cc032c01b0068019003c005
def ridgeSupport73_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport73_code
def ridgeSupport73_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport73_code
def ridgeSupport73_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport73_code
def ridgeSupport73_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport73_code
def ridgeSupport73_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport73_code
def ridgeSupport73_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport73_code
def ridgeSupport73_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport73_code
def ridgeSupport73_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport73_code
def ridgeSupport73_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport73_code
def ridgeSupport73_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport73_code
def ridgeSupport73_suffix_009 : List Nat := []
def ridgeSupport73_suffix_008 : List Nat := ridgeSupport73_008 ++ ridgeSupport73_suffix_009
def ridgeSupport73_suffix_007 : List Nat := ridgeSupport73_007 ++ ridgeSupport73_suffix_008
def ridgeSupport73_suffix_006 : List Nat := ridgeSupport73_006 ++ ridgeSupport73_suffix_007
def ridgeSupport73_suffix_005 : List Nat := ridgeSupport73_005 ++ ridgeSupport73_suffix_006
def ridgeSupport73_suffix_004 : List Nat := ridgeSupport73_004 ++ ridgeSupport73_suffix_005
def ridgeSupport73_suffix_003 : List Nat := ridgeSupport73_003 ++ ridgeSupport73_suffix_004
def ridgeSupport73_suffix_002 : List Nat := ridgeSupport73_002 ++ ridgeSupport73_suffix_003
def ridgeSupport73_suffix_001 : List Nat := ridgeSupport73_001 ++ ridgeSupport73_suffix_002
def ridgeSupport73_suffix_000 : List Nat := ridgeSupport73_000 ++ ridgeSupport73_suffix_001
theorem ridgeSupport73_source : candidateSupports 73 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport73_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
