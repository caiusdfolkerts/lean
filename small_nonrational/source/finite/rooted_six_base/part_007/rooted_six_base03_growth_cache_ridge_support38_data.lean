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
def ridgeSupport38_000 : List Nat := [0,31,32,33,34,541,542,543,544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567]
def ridgeSupport38_001 : List Nat := [568,569,570,571,572,573,574,575,576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599]
def ridgeSupport38_002 : List Nat := [600,601,602,603,604,605,606,607,608,609,610,611,612,3270,3271,3272,3273,3274,3275,3276,3277,3278,3279,3280,3281,3282,3283,3284,3285,3286,3287,3288]
def ridgeSupport38_003 : List Nat := [3289,3290,3291,3292,3293,3294,3295,3296,3297,3298,3299,3300,3301,3302,3303,3304,3305,3306,3307,3308,3309,3310,3311,3312,3313,3314,3315,3316,3317,3318,3319,3320]
def ridgeSupport38_004 : List Nat := [3321,3322,3323,3324,3325,3326,3327,3328,3329,3330,3331,3332,3333,3334,3335,3336,3337,3338,3339,3340,3341,3342,3343,3344,3345,3346,3347,3348,3349,3350,3351,3352]
def ridgeSupport38_005 : List Nat := [3353,3354,3355,3356,3357,3358,3359,3360,3361,3362,3363,3364,3365,3366,3367,3368,3369,3370,3371,3372,3373,3374,3375,3376,3377,3378,3379,3380,3381,3382,3383,3384]
def ridgeSupport38_006 : List Nat := [3385,3386,3387,3388,3389,3390,3391,3392,3393,3394,3395,3396,3397,3398,3399,3400,3401,3402,3403,3404,3405,3406,3407,3408,3409,3410,3411,3412,3413,3414,3415,3416]
def ridgeSupport38_007 : List Nat := [3417,3418,3419,3420,3421,3422,3423,3424,3425,3426,3427,3428,3429,3430,3431,3432,3433,3434,3435,3436,3437,3438,3439,3440,3441,3442,3443,3444,3445,3446,3447,3448]
def ridgeSupport38_008 : List Nat := [3449,3450,3451,3452,3453,3454,3455,3456,3457,3458,3459,3460,3461,3462,3463,3464,3465,3466,3467,3468,3469,3470,3471,3472,3473,3474,3475,3476,3477,3478,3479,3480]
def ridgeSupport38_009 : List Nat := [3481,3482,3483,3484,3485,4554,4555,4556,4557,4558,4559,4560,4561,4562,4563,4564,4565,4566,4567,4568,4569,4570,4571,4572,4573,4574,4575,4576,4577,5070,5071,5072]
def ridgeSupport38_010 : List Nat := [5073,5074,5075,5076,5077,5078,5079,5080,5081,5082,5083,5084,5085,5086,5087,5088,5089,5090,5091,5092,5093]
def ridgeSupport38_code : Nat := 0x13e59f24f8e7c53e19f04f7e7bd3dd9ee4f6e7b53d99ec4f5e7ad3d59ea4f4e7a53d19e84f3e79d1e18f0477e3bd1dd8ee476e3b51d98ec475e3ad1d58ea474e3a51d18e8473e39d1cd8e6472e394d9d6ce366db34d996cc365db2cd956ca364db24d916c8363db1cd8d6c6362db14d896c4361db0cd856c2360db04d816c035fdafcd7d6be35edaf4d796bc35ddaecd756ba35cdae4d716b835bdadcd6d6b635adad4d696b4359daccd656b2358dac4d616b0357dabcd5d6ae356dab4d596ac355daacd556aa354daa4d516a8353da9cd4d6a6352da94d496a4351da8cd456a2350da84d416a034fda7cd3d69e34eda74d3969c34dda6cd3569a34cda64d3169834bda5cd2d69634ada54d29694349da4cd25692348da44d21690347da3cd1d68e346da34d1968c345da2cd1568a344da24d11688343da1cd0d686342da14d09684341da0cd05682340da04d0168033fd9fccfd67e33ed9f4cf967c33dd9eccf567a33cd9e4cf167833bd9dcced67633ad9d4ce9674339d9ccce5672338d9c4ce1670337d9bccdd66e336d9b4cd966c335d9accd566a334d9a4cd1668333d99cccd666332d994cc9664331d98c26413189884c226012f89784ba25c12d89684b225812b89584aa25412989484a2250127893849a24c1258928492248123891848a244121890848224011f88f847a23c11d88e847223811b88d846a23411988c846223011788b845a22c11588a8452228113889844a224111888844222010f887843a022010808003e000
def ridgeSupport38_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport38_code
def ridgeSupport38_rest_001 : Nat := PackedRawNatGrowth.drop 416 ridgeSupport38_code
def ridgeSupport38_rest_002 : Nat := PackedRawNatGrowth.drop 832 ridgeSupport38_code
def ridgeSupport38_rest_003 : Nat := PackedRawNatGrowth.drop 1248 ridgeSupport38_code
def ridgeSupport38_rest_004 : Nat := PackedRawNatGrowth.drop 1664 ridgeSupport38_code
def ridgeSupport38_rest_005 : Nat := PackedRawNatGrowth.drop 2080 ridgeSupport38_code
def ridgeSupport38_rest_006 : Nat := PackedRawNatGrowth.drop 2496 ridgeSupport38_code
def ridgeSupport38_rest_007 : Nat := PackedRawNatGrowth.drop 2912 ridgeSupport38_code
def ridgeSupport38_rest_008 : Nat := PackedRawNatGrowth.drop 3328 ridgeSupport38_code
def ridgeSupport38_rest_009 : Nat := PackedRawNatGrowth.drop 3744 ridgeSupport38_code
def ridgeSupport38_rest_010 : Nat := PackedRawNatGrowth.drop 4160 ridgeSupport38_code
def ridgeSupport38_rest_011 : Nat := PackedRawNatGrowth.drop 4433 ridgeSupport38_code
def ridgeSupport38_suffix_011 : List Nat := []
def ridgeSupport38_suffix_010 : List Nat := ridgeSupport38_010 ++ ridgeSupport38_suffix_011
def ridgeSupport38_suffix_009 : List Nat := ridgeSupport38_009 ++ ridgeSupport38_suffix_010
def ridgeSupport38_suffix_008 : List Nat := ridgeSupport38_008 ++ ridgeSupport38_suffix_009
def ridgeSupport38_suffix_007 : List Nat := ridgeSupport38_007 ++ ridgeSupport38_suffix_008
def ridgeSupport38_suffix_006 : List Nat := ridgeSupport38_006 ++ ridgeSupport38_suffix_007
def ridgeSupport38_suffix_005 : List Nat := ridgeSupport38_005 ++ ridgeSupport38_suffix_006
def ridgeSupport38_suffix_004 : List Nat := ridgeSupport38_004 ++ ridgeSupport38_suffix_005
def ridgeSupport38_suffix_003 : List Nat := ridgeSupport38_003 ++ ridgeSupport38_suffix_004
def ridgeSupport38_suffix_002 : List Nat := ridgeSupport38_002 ++ ridgeSupport38_suffix_003
def ridgeSupport38_suffix_001 : List Nat := ridgeSupport38_001 ++ ridgeSupport38_suffix_002
def ridgeSupport38_suffix_000 : List Nat := ridgeSupport38_000 ++ ridgeSupport38_suffix_001
theorem ridgeSupport38_source : candidateSupports 38 =
    (PackedRawNatGrowth.readList 13 341 ridgeSupport38_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixBase03
