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
def ridgeSupport74_000 : List Nat := [5,45,49,50,51,202,205,207,210,212,214,217,219,222,224,226,229,231,234,236,780,782,783,786,788,792,794,795,798,800,804,806]
def ridgeSupport74_001 : List Nat := [807,810,812,852,853,855,856,857,858,860,861,863,864,866,867,873,874,876,877,878,879,881,882,884,885,887,888,894,895,897,898,899]
def ridgeSupport74_002 : List Nat := [900,902,903,905,906,908,909,3112,3113,3114,3115,3116,3117,3118,3119,3124,3125,3130,3131,3136,3137,3138,3139,3140,3141,3142,3143,3148,3149,3154,3155,3160]
def ridgeSupport74_003 : List Nat := [3161,3162,3163,3164,3165,3184,3185,3186,3187,3188,3189,3208,3209,3210,3211,3212,3213,3232,3233,3234,3235,3236,3237,3256,3257,3258,3259,3260,3261,3280,3281,3282]
def ridgeSupport74_004 : List Nat := [3283,3284,3285,3304,3305,3306,3307,3308,3309,3313,3315,3319,3321,3325,3327,3370,3371,3382,3383,3391,3393,3397,3399,3406,3407,3418,3419,3442,3443,3454,3455,3463]
def ridgeSupport74_005 : List Nat := [3465,3469,3471,3478,3479,3490,3491,3514,3515,3526,3527,3535,3537,3541,3543,3550,3551,3562,3563,5176,5177,5188,5189,5212,5213,5224,5225,5239,5241,5245,5247,5248]
def ridgeSupport74_006 : List Nat := [5249,5260,5261,5284,5285,5296,5297,5311,5313,5317,5319,5320,5321,5332,5333,5356,5357,5368,5369,5383,5385,5389,5391,7216,7217,7218,7219,7220,7221,7936,7937,7938]
def ridgeSupport74_007 : List Nat := [7939,7940,7941,7960,7961,7962,7963,7964,7965,7972,7973,7974,7975,7976,7977,7984,7985,7990,7991,8002,8003,8008,8009,8020,8021,8026,8027,8401,8403,8407,8409,8419]
cert_ridgeSupport_7 74 008 8421 8425 8427 8437 8439 8443 8445
cert_ridgeSupport_code_3 74
cert_ridgeSupport_rest_2 74 000 0
cert_ridgeSupport_rest_2 74 001 448
cert_ridgeSupport_rest_2 74 002 896
cert_ridgeSupport_rest_2 74 003 1344
cert_ridgeSupport_rest_2 74 004 1792
cert_ridgeSupport_rest_2 74 005 2240
cert_ridgeSupport_rest_2 74 006 2688
cert_ridgeSupport_rest_2 74 007 3136
cert_ridgeSupport_rest_2 74 008 3584
cert_ridgeSupport_rest_2 74 009 3682
cert_ridgeSupport_suffix_4 74 009
cert_ridgeSupport_suffix_3 74 008 009
cert_ridgeSupport_suffix_3 74 007 008
cert_ridgeSupport_suffix_3 74 006 007
cert_ridgeSupport_suffix_3 74 005 006
cert_ridgeSupport_suffix_3 74 004 005
cert_ridgeSupport_suffix_3 74 003 004
cert_ridgeSupport_suffix_3 74 002 003
cert_ridgeSupport_suffix_3 74 001 002
cert_ridgeSupport_suffix_3 74 000 001
cert_ridgeSupport_source_3 74 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
