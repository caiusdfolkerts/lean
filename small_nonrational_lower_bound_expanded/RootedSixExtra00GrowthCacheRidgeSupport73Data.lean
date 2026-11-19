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
def ridgeSupport73_000 : List Nat := [5,15,25,26,27,203,204,207,208,213,215,216,219,220,225,227,228,231,232,237,359,360,363,364,369,371,372,375,376,381,383,384]
def ridgeSupport73_001 : List Nat := [387,388,393,515,516,518,519,520,521,523,524,526,527,529,530,536,537,539,540,541,542,544,545,547,548,550,551,557,558,560,561,562]
def ridgeSupport73_002 : List Nat := [563,565,566,568,569,571,572,2872,2873,2874,2875,2876,2877,2878,2879,2884,2885,2890,2891,2896,2897,2898,2899,2900,2901,2902,2903,2908,2909,2914,2915,2920]
def ridgeSupport73_003 : List Nat := [2921,2922,2923,2924,2925,2944,2945,2946,2947,2948,2949,2968,2969,2970,2971,2972,2973,2992,2993,2994,2995,2996,2997,3016,3017,3018,3019,3020,3021,3040,3041,3042]
def ridgeSupport73_004 : List Nat := [3043,3044,3045,3064,3065,3066,3067,3068,3069,3073,3075,3079,3081,3085,3087,3358,3359,3376,3377,3394,3395,3403,3405,3409,3411,3412,3413,3430,3431,3448,3449,3466]
def ridgeSupport73_005 : List Nat := [3467,3475,3477,3481,3483,3484,3485,3502,3503,3520,3521,3538,3539,3547,3549,3553,3555,3556,3557,3886,3887,3904,3905,3922,3923,3931,3933,3937,3939,3940,3941,3958]
def ridgeSupport73_006 : List Nat := [3959,3976,3977,3994,3995,4003,4005,4009,4011,4012,4013,4030,4031,4048,4049,4066,4067,4075,4077,4081,4083,4084,4085,7180,7181,7182,7183,7184,7185,7888,7889,7890]
def ridgeSupport73_007 : List Nat := [7891,7892,7893,7912,7913,7914,7915,7916,7917,7924,7925,7926,7927,7928,7929,7987,7989,7996,7997,8005,8007,8014,8015,8023,8025,8032,8033,8107,8109,8116,8117,8125]
cert_ridgeSupport_7 73 008 8127 8134 8135 8143 8145 8152 8153
cert_ridgeSupport_code_3 73
cert_ridgeSupport_rest_2 73 000 0
cert_ridgeSupport_rest_2 73 001 448
cert_ridgeSupport_rest_2 73 002 896
cert_ridgeSupport_rest_2 73 003 1344
cert_ridgeSupport_rest_2 73 004 1792
cert_ridgeSupport_rest_2 73 005 2240
cert_ridgeSupport_rest_2 73 006 2688
cert_ridgeSupport_rest_2 73 007 3136
cert_ridgeSupport_rest_2 73 008 3584
cert_ridgeSupport_rest_2 73 009 3682
cert_ridgeSupport_suffix_4 73 009
cert_ridgeSupport_suffix_3 73 008 009
cert_ridgeSupport_suffix_3 73 007 008
cert_ridgeSupport_suffix_3 73 006 007
cert_ridgeSupport_suffix_3 73 005 006
cert_ridgeSupport_suffix_3 73 004 005
cert_ridgeSupport_suffix_3 73 003 004
cert_ridgeSupport_suffix_3 73 002 003
cert_ridgeSupport_suffix_3 73 001 002
cert_ridgeSupport_suffix_3 73 000 001
cert_ridgeSupport_source_3 73 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
