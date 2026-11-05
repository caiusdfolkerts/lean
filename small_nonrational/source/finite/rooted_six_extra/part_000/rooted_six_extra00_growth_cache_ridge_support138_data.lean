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
def ridgeSupport138_000 : List Nat := [6,46,49,52,53,203,204,206,211,213,238,241,243,246,248,250,253,255,258,260,779,781,784,785,787,816,818,819,822,824,828,830]
def ridgeSupport138_001 : List Nat := [831,834,836,851,853,854,856,857,859,861,862,864,865,868,869,872,874,875,877,878,880,882,883,885,886,889,890,915,916,918,919,920]
def ridgeSupport138_002 : List Nat := [921,923,924,926,927,929,930,3112,3113,3118,3119,3120,3121,3122,3123,3126,3127,3132,3133,3136,3137,3142,3143,3144,3145,3146,3147,3150,3151,3156,3157,3166]
def ridgeSupport138_003 : List Nat := [3167,3168,3169,3170,3171,3190,3191,3192,3193,3194,3195,3214,3215,3216,3217,3218,3219,3238,3239,3240,3241,3242,3243,3262,3263,3264,3265,3266,3267,3286,3287,3288]
def ridgeSupport138_004 : List Nat := [3289,3290,3291,3307,3309,3310,3311,3312,3313,3314,3315,3317,3320,3323,3326,3372,3373,3384,3385,3389,3392,3395,3398,3408,3409,3420,3421,3444,3445,3456,3457,3461]
def ridgeSupport138_005 : List Nat := [3464,3467,3470,3480,3481,3492,3493,3586,3587,3598,3599,3607,3609,3613,3615,3622,3623,3634,3635,5178,5179,5190,5191,5214,5215,5226,5227,5237,5240,5243,5246,5250]
def ridgeSupport138_006 : List Nat := [5251,5262,5263,5286,5287,5298,5299,5309,5312,5315,5318,5392,5393,5404,5405,5428,5429,5440,5441,5455,5457,5461,5463,7222,7223,7224,7225,7226,7227,7942,7943,7944]
def ridgeSupport138_007 : List Nat := [7945,7946,7947,7963,7965,7966,7967,7968,7969,7975,7977,7978,7979,7980,7981,7986,7987,7992,7993,8004,8005,8010,8011,8038,8039,8044,8045,8399,8402,8405,8408,8417]
def ridgeSupport138_008 : List Nat := [8420,8423,8426,8455,8457,8461,8463]
def ridgeSupport138_code : Nat := 0x210f8436109841e0ea839e0e483860d883560d2833df6d7db1f677d99f4b7d29f457d11f397ce1f337cc9f2d7cb1f2b7ca9f297c9df217c81f1f7c79f1d7c6df0b7c29f097c21f077c19c3b70e9c3970e1c3770d95575555551553d541550153554d151d547151154414c6530d4c052f54b352c94a7529948f5239483520947e51ed47851d546b51a945f5179447511943b50e8e3338c8e273898e1f3874e19385ce0f3838e033808da53690d993660d8e362cd883614d813600d7535d0d5d3570d513540d46350cd4034f4d3934e0d2d34b0cfe33eccf833d4cf333c8cf133c0cef33b8ced33accdb3368cd93360cd73358cc33308cc13300cbf32f8cab32a8ca932a0ca73298c933248c913240c8f3238c7b31e8c7931e0c7731d8c633188c613180c5f3178c553150c4f3138c4b3128c493120c473118c413100c3d30f0c3730d8c3330c8c3130c0c2f30b8c2930a03a20e8439f0e7839c0e6c3990e603970e583940e4c37a0de43760dd43730dc83700db836d0dac36a0da03650d903610d8035e0d7435b0d643580d583550d4c3440d0833f0cf833c0ce03360ccc3320cc03130c443100c3430b041010203fc0fd03e80f803d80f303c40ee03540d303380cc032c03500d003100b8006
def ridgeSupport138_rest_000 : Nat := PackedRawNatGrowth.drop 0 ridgeSupport138_code
def ridgeSupport138_rest_001 : Nat := PackedRawNatGrowth.drop 448 ridgeSupport138_code
def ridgeSupport138_rest_002 : Nat := PackedRawNatGrowth.drop 896 ridgeSupport138_code
def ridgeSupport138_rest_003 : Nat := PackedRawNatGrowth.drop 1344 ridgeSupport138_code
def ridgeSupport138_rest_004 : Nat := PackedRawNatGrowth.drop 1792 ridgeSupport138_code
def ridgeSupport138_rest_005 : Nat := PackedRawNatGrowth.drop 2240 ridgeSupport138_code
def ridgeSupport138_rest_006 : Nat := PackedRawNatGrowth.drop 2688 ridgeSupport138_code
def ridgeSupport138_rest_007 : Nat := PackedRawNatGrowth.drop 3136 ridgeSupport138_code
def ridgeSupport138_rest_008 : Nat := PackedRawNatGrowth.drop 3584 ridgeSupport138_code
def ridgeSupport138_rest_009 : Nat := PackedRawNatGrowth.drop 3682 ridgeSupport138_code
def ridgeSupport138_suffix_009 : List Nat := []
def ridgeSupport138_suffix_008 : List Nat := ridgeSupport138_008 ++ ridgeSupport138_suffix_009
def ridgeSupport138_suffix_007 : List Nat := ridgeSupport138_007 ++ ridgeSupport138_suffix_008
def ridgeSupport138_suffix_006 : List Nat := ridgeSupport138_006 ++ ridgeSupport138_suffix_007
def ridgeSupport138_suffix_005 : List Nat := ridgeSupport138_005 ++ ridgeSupport138_suffix_006
def ridgeSupport138_suffix_004 : List Nat := ridgeSupport138_004 ++ ridgeSupport138_suffix_005
def ridgeSupport138_suffix_003 : List Nat := ridgeSupport138_003 ++ ridgeSupport138_suffix_004
def ridgeSupport138_suffix_002 : List Nat := ridgeSupport138_002 ++ ridgeSupport138_suffix_003
def ridgeSupport138_suffix_001 : List Nat := ridgeSupport138_001 ++ ridgeSupport138_suffix_002
def ridgeSupport138_suffix_000 : List Nat := ridgeSupport138_000 ++ ridgeSupport138_suffix_001
theorem ridgeSupport138_source : candidateSupports 138 =
    (PackedRawNatGrowth.readList 14 263 ridgeSupport138_code).1 := by rfl

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
