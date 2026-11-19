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
def ridgeSupport521_000 : List Nat := [8,18,27,29,30,226,229,230,233,236,250,253,254,257,260,262,265,266,269,272,382,385,386,389,392,406,409,410,413,416,418,421]
def ridgeSupport521_001 : List Nat := [422,425,428,535,536,538,539,542,543,544,546,547,549,554,555,556,557,559,560,563,564,565,567,568,570,575,576,577,578,580,581,584]
def ridgeSupport521_002 : List Nat := [585,586,588,589,591,596,597,2876,2877,2882,2883,2888,2889,2890,2891,2892,2893,2894,2895,2900,2901,2906,2907,2912,2913,2914,2915,2916,2917,2918,2919,2938]
def ridgeSupport521_003 : List Nat := [2939,2940,2941,2942,2943,2962,2963,2964,2965,2966,2967,2986,2987,2988,2989,2990,2991,3010,3011,3012,3013,3014,3015,3034,3035,3036,3037,3038,3039,3058,3059,3060]
def ridgeSupport521_004 : List Nat := [3061,3062,3063,3064,3066,3070,3072,3076,3078,3082,3083,3084,3085,3086,3087,3434,3435,3452,3453,3470,3471,3472,3474,3478,3480,3488,3489,3506,3507,3524,3525,3542]
def ridgeSupport521_005 : List Nat := [3543,3544,3546,3550,3552,3560,3561,3578,3579,3596,3597,3614,3615,3616,3618,3622,3624,3632,3633,3962,3963,3980,3981,3998,3999,4000,4002,4006,4008,4016,4017,4034]
def ridgeSupport521_006 : List Nat := [4035,4052,4053,4070,4071,4072,4074,4078,4080,4088,4089,4106,4107,4124,4125,4142,4143,4144,4146,4150,4152,4160,4161,7198,7199,7200,7201,7202,7203,7906,7907,7908]
def ridgeSupport521_007 : List Nat := [7909,7910,7911,7912,7914,7918,7920,7922,7923,7924,7926,7930,7932,7934,7935,8002,8004,8018,8019,8020,8022,8036,8037,8038,8040,8054,8055,8122,8124,8138,8139,8140]
cert_ridgeSupport_7 521 008 8142 8156 8157 8158 8160 8174 8175
cert_ridgeSupport_code_3 521
cert_ridgeSupport_rest_2 521 000 0
cert_ridgeSupport_rest_2 521 001 448
cert_ridgeSupport_rest_2 521 002 896
cert_ridgeSupport_rest_2 521 003 1344
cert_ridgeSupport_rest_2 521 004 1792
cert_ridgeSupport_rest_2 521 005 2240
cert_ridgeSupport_rest_2 521 006 2688
cert_ridgeSupport_rest_2 521 007 3136
cert_ridgeSupport_rest_2 521 008 3584
cert_ridgeSupport_rest_2 521 009 3682
cert_ridgeSupport_suffix_4 521 009
cert_ridgeSupport_suffix_3 521 008 009
cert_ridgeSupport_suffix_3 521 007 008
cert_ridgeSupport_suffix_3 521 006 007
cert_ridgeSupport_suffix_3 521 005 006
cert_ridgeSupport_suffix_3 521 004 005
cert_ridgeSupport_suffix_3 521 003 004
cert_ridgeSupport_suffix_3 521 002 003
cert_ridgeSupport_suffix_3 521 001 002
cert_ridgeSupport_suffix_3 521 000 001
cert_ridgeSupport_source_3 521 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
