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
def ridgeSupport522_000 : List Nat := [8,48,51,53,54,227,228,230,235,237,251,252,254,259,261,263,264,266,271,273,803,805,808,809,811,827,829,832,833,835,839,841]
def ridgeSupport522_001 : List Nat := [844,845,847,872,873,875,876,879,880,881,883,884,886,891,892,893,894,896,897,900,901,902,904,905,907,912,913,914,915,917,918,921]
def ridgeSupport522_002 : List Nat := [922,923,925,926,928,933,934,3116,3117,3122,3123,3128,3129,3130,3131,3132,3133,3134,3135,3140,3141,3146,3147,3152,3153,3154,3155,3156,3157,3158,3159,3178]
def ridgeSupport522_003 : List Nat := [3179,3180,3181,3182,3183,3202,3203,3204,3205,3206,3207,3226,3227,3228,3229,3230,3231,3250,3251,3252,3253,3254,3255,3274,3275,3276,3277,3278,3279,3298,3299,3300]
def ridgeSupport522_004 : List Nat := [3301,3302,3303,3304,3306,3310,3312,3316,3318,3322,3323,3324,3325,3326,3327,3446,3447,3458,3459,3460,3462,3466,3468,3482,3483,3494,3495,3518,3519,3530,3531,3532]
def ridgeSupport522_005 : List Nat := [3534,3538,3540,3554,3555,3566,3567,3590,3591,3602,3603,3604,3606,3610,3612,3626,3627,3638,3639,5252,5253,5264,5265,5288,5289,5300,5301,5308,5310,5314,5316,5324]
def ridgeSupport522_006 : List Nat := [5325,5336,5337,5360,5361,5372,5373,5380,5382,5386,5388,5396,5397,5408,5409,5432,5433,5444,5445,5452,5454,5458,5460,7234,7235,7236,7237,7238,7239,7954,7955,7956]
def ridgeSupport522_007 : List Nat := [7957,7958,7959,7960,7962,7966,7968,7970,7971,7972,7974,7978,7980,7982,7983,8006,8007,8012,8013,8024,8025,8030,8031,8042,8043,8048,8049,8416,8418,8422,8424,8434]
cert_ridgeSupport_7 522 008 8436 8440 8442 8452 8454 8458 8460
cert_ridgeSupport_code_3 522
cert_ridgeSupport_rest_2 522 000 0
cert_ridgeSupport_rest_2 522 001 448
cert_ridgeSupport_rest_2 522 002 896
cert_ridgeSupport_rest_2 522 003 1344
cert_ridgeSupport_rest_2 522 004 1792
cert_ridgeSupport_rest_2 522 005 2240
cert_ridgeSupport_rest_2 522 006 2688
cert_ridgeSupport_rest_2 522 007 3136
cert_ridgeSupport_rest_2 522 008 3584
cert_ridgeSupport_rest_2 522 009 3682
cert_ridgeSupport_suffix_4 522 009
cert_ridgeSupport_suffix_3 522 008 009
cert_ridgeSupport_suffix_3 522 007 008
cert_ridgeSupport_suffix_3 522 006 007
cert_ridgeSupport_suffix_3 522 005 006
cert_ridgeSupport_suffix_3 522 004 005
cert_ridgeSupport_suffix_3 522 003 004
cert_ridgeSupport_suffix_3 522 002 003
cert_ridgeSupport_suffix_3 522 001 002
cert_ridgeSupport_suffix_3 522 000 001
cert_ridgeSupport_source_3 522 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
