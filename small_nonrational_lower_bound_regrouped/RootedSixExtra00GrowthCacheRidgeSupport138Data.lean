module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public meta import CertificateNumbers
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
cert_ridgeSupport_7 138 008 8420 8423 8426 8455 8457 8461 8463
cert_ridgeSupport_code_3 138
cert_ridgeSupport_rest_2 138 000 0
cert_ridgeSupport_rest_2 138 001 448
cert_ridgeSupport_rest_2 138 002 896
cert_ridgeSupport_rest_2 138 003 1344
cert_ridgeSupport_rest_2 138 004 1792
cert_ridgeSupport_rest_2 138 005 2240
cert_ridgeSupport_rest_2 138 006 2688
cert_ridgeSupport_rest_2 138 007 3136
cert_ridgeSupport_rest_2 138 008 3584
cert_ridgeSupport_rest_2 138 009 3682
cert_ridgeSupport_suffix_4 138 009
cert_ridgeSupport_suffix_3 138 008 009
cert_ridgeSupport_suffix_3 138 007 008
cert_ridgeSupport_suffix_3 138 006 007
cert_ridgeSupport_suffix_3 138 005 006
cert_ridgeSupport_suffix_3 138 004 005
cert_ridgeSupport_suffix_3 138 003 004
cert_ridgeSupport_suffix_3 138 002 003
cert_ridgeSupport_suffix_3 138 001 002
cert_ridgeSupport_suffix_3 138 000 001
cert_ridgeSupport_source_3 138 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
