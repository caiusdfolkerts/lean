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
def ridgeSupport265_000 : List Nat := [7,17,26,28,30,214,217,218,221,224,238,241,242,245,248,263,264,267,268,273,370,373,374,377,380,394,397,398,401,404,419,420]
def ridgeSupport265_001 : List Nat := [423,424,429,514,515,517,518,521,522,523,525,526,528,533,534,556,558,559,561,562,564,566,567,569,570,573,574,577,579,580,582,583]
def ridgeSupport265_002 : List Nat := [585,587,588,590,591,594,595,2874,2875,2880,2881,2884,2885,2886,2887,2888,2889,2894,2895,2898,2899,2904,2905,2908,2909,2910,2911,2912,2913,2918,2919,2932]
def ridgeSupport265_003 : List Nat := [2933,2934,2935,2936,2937,2956,2957,2958,2959,2960,2961,2980,2981,2982,2983,2984,2985,3004,3005,3006,3007,3008,3009,3028,3029,3030,3031,3032,3033,3052,3053,3054]
def ridgeSupport265_004 : List Nat := [3055,3056,3057,3065,3068,3071,3074,3076,3077,3078,3079,3080,3081,3082,3084,3362,3363,3380,3381,3398,3399,3400,3402,3406,3408,3416,3417,3504,3505,3522,3523,3540]
def ridgeSupport265_005 : List Nat := [3541,3545,3548,3551,3554,3558,3559,3576,3577,3594,3595,3612,3613,3617,3620,3623,3626,3630,3631,3890,3891,3908,3909,3926,3927,3928,3930,3934,3936,3944,3945,4032]
def ridgeSupport265_006 : List Nat := [4033,4050,4051,4068,4069,4073,4076,4079,4082,4086,4087,4104,4105,4122,4123,4140,4141,4145,4148,4151,4154,4158,4159,7192,7193,7194,7195,7196,7197,7900,7901,7902]
def ridgeSupport265_007 : List Nat := [7903,7904,7905,7913,7916,7919,7921,7922,7923,7925,7928,7931,7933,7934,7935,7984,7986,8000,8001,8021,8024,8034,8035,8039,8042,8052,8053,8104,8106,8120,8121,8141]
cert_ridgeSupport_7 265 008 8144 8154 8155 8159 8162 8172 8173
cert_ridgeSupport_code_3 265
cert_ridgeSupport_rest_2 265 000 0
cert_ridgeSupport_rest_2 265 001 448
cert_ridgeSupport_rest_2 265 002 896
cert_ridgeSupport_rest_2 265 003 1344
cert_ridgeSupport_rest_2 265 004 1792
cert_ridgeSupport_rest_2 265 005 2240
cert_ridgeSupport_rest_2 265 006 2688
cert_ridgeSupport_rest_2 265 007 3136
cert_ridgeSupport_rest_2 265 008 3584
cert_ridgeSupport_rest_2 265 009 3682
cert_ridgeSupport_suffix_4 265 009
cert_ridgeSupport_suffix_3 265 008 009
cert_ridgeSupport_suffix_3 265 007 008
cert_ridgeSupport_suffix_3 265 006 007
cert_ridgeSupport_suffix_3 265 005 006
cert_ridgeSupport_suffix_3 265 004 005
cert_ridgeSupport_suffix_3 265 003 004
cert_ridgeSupport_suffix_3 265 002 003
cert_ridgeSupport_suffix_3 265 001 002
cert_ridgeSupport_suffix_3 265 000 001
cert_ridgeSupport_source_3 265 14 263
end Papers.RationalityTen.RootedCaches.RootedSixExtra00
