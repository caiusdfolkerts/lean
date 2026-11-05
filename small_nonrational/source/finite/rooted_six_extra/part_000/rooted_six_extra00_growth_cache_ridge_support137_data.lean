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
def ridgeSupport137_000 : List Nat := [6,16,25,28,29,202,205,206,209,212,239,240,243,244,249,251,252,255,256,261,358,361,362,365,368,395,396,399,400,405,407,408]
def ridgeSupport137_001 : List Nat := [411,412,417,514,516,517,519,520,522,524,525,527,528,531,532,535,537,538,540,541,543,545,546,548,549,552,553,578,579,581,582,583]
def ridgeSupport137_002 : List Nat := [584,586,587,589,590,592,593,2872,2873,2878,2879,2880,2881,2882,2883,2886,2887,2892,2893,2896,2897,2902,2903,2904,2905,2906,2907,2910,2911,2916,2917,2926]
def ridgeSupport137_003 : List Nat := [2927,2928,2929,2930,2931,2950,2951,2952,2953,2954,2955,2974,2975,2976,2977,2978,2979,2998,2999,3000,3001,3002,3003,3022,3023,3024,3025,3026,3027,3046,3047,3048]
def ridgeSupport137_004 : List Nat := [3049,3050,3051,3067,3069,3070,3071,3072,3073,3074,3075,3077,3080,3083,3086,3360,3361,3378,3379,3396,3397,3401,3404,3407,3410,3414,3415,3432,3433,3450,3451,3468]
def ridgeSupport137_005 : List Nat := [3469,3473,3476,3479,3482,3486,3487,3574,3575,3592,3593,3610,3611,3619,3621,3625,3627,3628,3629,3888,3889,3906,3907,3924,3925,3929,3932,3935,3938,3942,3943,3960]
def ridgeSupport137_006 : List Nat := [3961,3978,3979,3996,3997,4001,4004,4007,4010,4014,4015,4102,4103,4120,4121,4138,4139,4147,4149,4153,4155,4156,4157,7186,7187,7188,7189,7190,7191,7894,7895,7896]
def ridgeSupport137_007 : List Nat := [7897,7898,7899,7915,7917,7918,7919,7920,7921,7927,7929,7930,7931,7932,7933,7985,7988,7998,7999,8003,8006,8016,8017,8041,8043,8050,8051,8105,8108,8118,8119,8123]
def ridgeSupport137_008 : List Nat := [8126,8136,8137,8161,8163,8170,8171]
def ridgeSupport137_code : Nat := 0x1feb7fa9fe37f85fc97f21fbe7eedfb77ed9fac7ea5f737dc9f6b7da5f517d41f467d0df3f7cf9f347cc5efd7bf1efb7be9ef97bddef17bc1eef7bb9eed7badedb7b69ed97b61ed77b59c177059c157051c13704903d40f103b40e503540cd02b40a901940610074018faf3eb8faa3e9cfa43e84f9d3e70f8b3e28f793de0f673d98f623d7cf5c3d64f553d50f433d08f313cc0e2d38b0e2b38a4e25388ce1b3868e093820df737d8d9f3678d9a365cd943644d8d3630d7b35e8d6935a0d573558d52353cd4c3524d453510d3334c8d213480c0e302cc083014c033008c013000bff2ff8bfd2fecbeb2fa8be92fa0be72f98bd32f48bd12f40bcf2f38bbb2ee8bb92ee0bb72ed8ba32e88ba12e80b9f2e78b8b2e28b892e20b872e18b732dc8b712dc0b6f2db8b652d90b5f2d78b5b2d68b592d60b572d58b512d40b4d2d30b472d18b432d08b412d00b3f2cf8b392ce0251094024e093424b0928248091c2460914243090822908a02250890222088421f087421c0868219085c214084c210083c20d083020a0820207081420408081a1067019b06601970654190063c18c062c17005b416a05a4166041410003fc0fc03ec0f903d00f303c00ef03500d103380cd032801d00700190040006
def ridgeSupport137_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport137_code
def ridgeSupport137_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport137_code
def ridgeSupport137_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport137_code
def ridgeSupport137_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport137_code
def ridgeSupport137_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport137_code
def ridgeSupport137_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport137_code
def ridgeSupport137_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport137_code
def ridgeSupport137_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport137_code
def ridgeSupport137_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport137_code
def ridgeSupport137_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport137_code
def ridgeSupport137_suffix_009 : List Nat := []
def ridgeSupport137_suffix_008 : List Nat := ridgeSupport137_008 ++ ridgeSupport137_suffix_009
def ridgeSupport137_suffix_007 : List Nat := ridgeSupport137_007 ++ ridgeSupport137_suffix_008
def ridgeSupport137_suffix_006 : List Nat := ridgeSupport137_006 ++ ridgeSupport137_suffix_007
def ridgeSupport137_suffix_005 : List Nat := ridgeSupport137_005 ++ ridgeSupport137_suffix_006
def ridgeSupport137_suffix_004 : List Nat := ridgeSupport137_004 ++ ridgeSupport137_suffix_005
def ridgeSupport137_suffix_003 : List Nat := ridgeSupport137_003 ++ ridgeSupport137_suffix_004
def ridgeSupport137_suffix_002 : List Nat := ridgeSupport137_002 ++ ridgeSupport137_suffix_003
def ridgeSupport137_suffix_001 : List Nat := ridgeSupport137_001 ++ ridgeSupport137_suffix_002
def ridgeSupport137_suffix_000 : List Nat := ridgeSupport137_000 ++ ridgeSupport137_suffix_001
theorem ridgeSupport137_source : candidateSupports 137 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport137_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
