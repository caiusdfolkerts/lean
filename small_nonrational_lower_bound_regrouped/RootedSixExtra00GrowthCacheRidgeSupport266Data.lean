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
def ridgeSupport266_000 : List Nat := [7,47,50,52,54,215,216,218,223,225,239,240,242,247,249,262,265,267,270,272,791,793,796,797,799,815,817,820,821,823,840,842]
def ridgeSupport266_001 : List Nat := [843,846,848,851,852,854,855,858,859,860,862,863,865,870,871,893,895,896,898,899,901,903,904,906,907,910,911,914,916,917,919,920]
def ridgeSupport266_002 : List Nat := [922,924,925,927,928,931,932,3114,3115,3120,3121,3124,3125,3126,3127,3128,3129,3134,3135,3138,3139,3144,3145,3148,3149,3150,3151,3152,3153,3158,3159,3172]
def ridgeSupport266_003 : List Nat := [3173,3174,3175,3176,3177,3196,3197,3198,3199,3200,3201,3220,3221,3222,3223,3224,3225,3244,3245,3246,3247,3248,3249,3268,3269,3270,3271,3272,3273,3292,3293,3294]
def ridgeSupport266_004 : List Nat := [3295,3296,3297,3305,3308,3311,3314,3316,3317,3318,3319,3320,3321,3322,3324,3374,3375,3386,3387,3388,3390,3394,3396,3410,3411,3422,3423,3516,3517,3528,3529,3533]
def ridgeSupport266_005 : List Nat := [3536,3539,3542,3552,3553,3564,3565,3588,3589,3600,3601,3605,3608,3611,3614,3624,3625,3636,3637,5180,5181,5192,5193,5216,5217,5228,5229,5236,5238,5242,5244,5322]
def ridgeSupport266_006 : List Nat := [5323,5334,5335,5358,5359,5370,5371,5381,5384,5387,5390,5394,5395,5406,5407,5430,5431,5442,5443,5453,5456,5459,5462,7228,7229,7230,7231,7232,7233,7948,7949,7950]
def ridgeSupport266_007 : List Nat := [7951,7952,7953,7961,7964,7967,7969,7970,7971,7973,7976,7979,7981,7982,7983,7988,7989,7994,7995,8022,8023,8028,8029,8040,8041,8046,8047,8398,8400,8404,8406,8435]
cert_ridgeSupport_7 266 008 8438 8441 8444 8453 8456 8459 8462
cert_ridgeSupport_code_3 266
cert_ridgeSupport_rest_2 266 000 0
cert_ridgeSupport_rest_2 266 001 448
cert_ridgeSupport_rest_2 266 002 896
cert_ridgeSupport_rest_2 266 003 1344
cert_ridgeSupport_rest_2 266 004 1792
cert_ridgeSupport_rest_2 266 005 2240
cert_ridgeSupport_rest_2 266 006 2688
cert_ridgeSupport_rest_2 266 007 3136
cert_ridgeSupport_rest_2 266 008 3584
cert_ridgeSupport_rest_2 266 009 3682
cert_ridgeSupport_suffix_4 266 009
cert_ridgeSupport_suffix_3 266 008 009
cert_ridgeSupport_suffix_3 266 007 008
cert_ridgeSupport_suffix_3 266 006 007
cert_ridgeSupport_suffix_3 266 005 006
cert_ridgeSupport_suffix_3 266 004 005
cert_ridgeSupport_suffix_3 266 003 004
cert_ridgeSupport_suffix_3 266 002 003
cert_ridgeSupport_suffix_3 266 001 002
cert_ridgeSupport_suffix_3 266 000 001
cert_ridgeSupport_source_3 266 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
