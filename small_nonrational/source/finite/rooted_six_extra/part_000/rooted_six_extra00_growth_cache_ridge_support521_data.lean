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
def ridgeSupport521_000 : List Nat := [8,18,27,29,30,226,229,230,233,236,250,253,254,257,260,262,265,266,269,272,382,385,386,389,392,406,409,410,413,416,418,421]
def ridgeSupport521_001 : List Nat := [422,425,428,535,536,538,539,542,543,544,546,547,549,554,555,556,557,559,560,563,564,565,567,568,570,575,576,577,578,580,581,584]
def ridgeSupport521_002 : List Nat := [585,586,588,589,591,596,597,2876,2877,2882,2883,2888,2889,2890,2891,2892,2893,2894,2895,2900,2901,2906,2907,2912,2913,2914,2915,2916,2917,2918,2919,2938]
def ridgeSupport521_003 : List Nat := [2939,2940,2941,2942,2943,2962,2963,2964,2965,2966,2967,2986,2987,2988,2989,2990,2991,3010,3011,3012,3013,3014,3015,3034,3035,3036,3037,3038,3039,3058,3059,3060]
def ridgeSupport521_004 : List Nat := [3061,3062,3063,3064,3066,3070,3072,3076,3078,3082,3083,3084,3085,3086,3087,3434,3435,3452,3453,3470,3471,3472,3474,3478,3480,3488,3489,3506,3507,3524,3525,3542]
def ridgeSupport521_005 : List Nat := [3543,3544,3546,3550,3552,3560,3561,3578,3579,3596,3597,3614,3615,3616,3618,3622,3624,3632,3633,3962,3963,3980,3981,3998,3999,4000,4002,4006,4008,4016,4017,4034]
def ridgeSupport521_006 : List Nat := [4035,4052,4053,4070,4071,4072,4074,4078,4080,4088,4089,4106,4107,4124,4125,4142,4143,4144,4146,4150,4152,4160,4161,7198,7199,7200,7201,7202,7203,7906,7907,7908]
def ridgeSupport521_007 : List Nat := [7909,7910,7911,7912,7914,7918,7920,7922,7923,7924,7926,7930,7932,7934,7935,8002,8004,8018,8019,8020,8022,8036,8037,8038,8040,8054,8055,8122,8124,8138,8139,8140]
def ridgeSupport521_008 : List Nat := [8142,8156,8157,8158,8160,8174,8175]
def ridgeSupport521_code : Nat := 0x1fef7fb9fe07f79fdd7f71fce7f31fcb7f29fbc7ee9f777dd9f687d99f657d91f567d51f537d49f447d09eff7bf9efc7be9ef67bd1ef37bc9ef07bb9eea7ba1ee77b99ee57b91ee37b89c237089c217081c1f7079041410103840d903240c102f40b901d407100b4028ff93fe0ff03fb8fea3fa0fe73f98fd53f50fc33f08fb13ec0fa83e98fa23e80f9f3e78f8d3e30f7b3de8e3138c0e283898e223880e1f3878e0d3830dfb37e8de937a0de03778dda3760dd73758dc53710db336c8da13680d983658d923640d8f3638d7d35f0d6b35a8c0f3038c0d3030c0b3028c063010c002ff8bfa2fe0bf72fd8bf52fd0bf32fc8bdf2f78bdd2f70bdb2f68bc72f18bc52f10bc32f08baf2eb8bad2eb0bab2ea8b972e58b952e50b932e48b7f2df8b7d2df0b7b2de8b672d98b652d90b632d88b612d80b5b2d68b552d50b4f2d38b4d2d30b4b2d28b492d20b432d08b3d2cf0255095024f093424c092824909202450910242090424008fc23a08e023708d423408cc23008bc22d08b022b08a8225088c222088021f087821b0868218085c1ac06a41a606941a2068019d066819906581880614182060417e044010d0428109041810404040fe03f40fa03b00e903980e5038801e007401b0048008
def ridgeSupport521_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport521_code
def ridgeSupport521_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport521_code
def ridgeSupport521_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport521_code
def ridgeSupport521_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport521_code
def ridgeSupport521_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport521_code
def ridgeSupport521_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport521_code
def ridgeSupport521_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport521_code
def ridgeSupport521_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport521_code
def ridgeSupport521_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport521_code
def ridgeSupport521_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport521_code
def ridgeSupport521_suffix_009 : List Nat := []
def ridgeSupport521_suffix_008 : List Nat := ridgeSupport521_008 ++ ridgeSupport521_suffix_009
def ridgeSupport521_suffix_007 : List Nat := ridgeSupport521_007 ++ ridgeSupport521_suffix_008
def ridgeSupport521_suffix_006 : List Nat := ridgeSupport521_006 ++ ridgeSupport521_suffix_007
def ridgeSupport521_suffix_005 : List Nat := ridgeSupport521_005 ++ ridgeSupport521_suffix_006
def ridgeSupport521_suffix_004 : List Nat := ridgeSupport521_004 ++ ridgeSupport521_suffix_005
def ridgeSupport521_suffix_003 : List Nat := ridgeSupport521_003 ++ ridgeSupport521_suffix_004
def ridgeSupport521_suffix_002 : List Nat := ridgeSupport521_002 ++ ridgeSupport521_suffix_003
def ridgeSupport521_suffix_001 : List Nat := ridgeSupport521_001 ++ ridgeSupport521_suffix_002
def ridgeSupport521_suffix_000 : List Nat := ridgeSupport521_000 ++ ridgeSupport521_suffix_001
theorem ridgeSupport521_source : candidateSupports 521 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport521_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
